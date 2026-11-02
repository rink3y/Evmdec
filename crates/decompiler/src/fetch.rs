//! Fetching a contract by address and assembling what it really is.
//!
//! A contract's code is rarely the whole story: a proxy forwards to an implementation, a
//! diamond routes each selector to a facet, and both call fixed addresses whose behaviour is
//! part of the contract's. This module fetches the code at an address, resolves the pattern it
//! implements, fetches the code it forwards to and composes the pieces into one
//! [`Contract`] ([`crate::decompile::compose`]) so the analyzer sees what callers see. It then
//! fetches the hard-coded dependencies and resolves each the same way, one level deep, so a
//! dependency that is itself a proxy appears as its implementation.

use crate::decompile::{self, Contract, Options, PartRole, ProxyRef};
use crate::rpc::{self, Client};
use crate::u256::U256;
use std::collections::HashSet;

/// What to fetch beyond the code at the address.
#[derive(Clone, Copy, Debug)]
pub struct Policy {
    /// Resolve proxies and diamonds and compose them with their code.
    pub follow: bool,
    /// Hard-coded call targets fetched per contract, at most.
    pub max_linked: usize,
    /// Code units fetched for one request, at most, across parts and dependencies.
    pub max_total: usize,
    /// Levels of hard-coded dependencies to follow: 1 fetches the contract's dependencies,
    /// each resolved as a proxy or diamond but with its own dependencies left alone.
    pub depth: usize,
}

impl Default for Policy {
    fn default() -> Self {
        Policy {
            follow: true,
            max_linked: 8,
            max_total: 24,
            depth: 1,
        }
    }
}

/// Fetch, resolve and compose the contract at `address` on `chain`. Progress lines go to
/// `log`; the result is the composed contract with its dependencies in `linked`.
pub fn fetch(
    client: &Client,
    address: &str,
    chain: &str,
    opts: &Options,
    policy: Policy,
    log: &mut dyn FnMut(String),
) -> Result<Contract, String> {
    let mut budget = Budget {
        seen: HashSet::new(),
        left: policy.max_total,
    };
    fetch_inner(
        client,
        address,
        chain,
        opts,
        policy,
        policy.depth,
        &mut budget,
        log,
    )
}

/// What one request may still fetch.
struct Budget {
    /// Addresses already fetched (lower-case).
    seen: HashSet<String>,
    /// Code units left to fetch.
    left: usize,
}

impl Budget {
    /// Claim a fetch of `address`; `false` when it was fetched already or nothing is left.
    fn take(&mut self, address: &str) -> bool {
        if self.left == 0 || !self.seen.insert(address.to_ascii_lowercase()) {
            return false;
        }
        self.left -= 1;
        true
    }
}

#[allow(clippy::too_many_arguments)]
fn fetch_inner(
    client: &Client,
    address: &str,
    chain: &str,
    opts: &Options,
    policy: Policy,
    depth: usize,
    budget: &mut Budget,
    log: &mut dyn FnMut(String),
) -> Result<Contract, String> {
    budget.take(address);
    log(format!("fetching code of {} on {}...", address, chain));
    let code = client.get_code(address)?;
    if code.is_empty() {
        return Err(format!(
            "{} has no code on {} (not a contract, or wrong chain)",
            address, chain
        ));
    }
    let mut c = decompile::decompile(&code, opts);
    c.address = Some(address.to_string());
    c.chain = Some(chain.to_string());
    if !policy.follow {
        return Ok(c);
    }
    c = resolve(client, c, &code, opts, budget, log)?;
    if depth > 0 {
        let own: Vec<String> = c
            .parts
            .iter()
            .map(|p| p.address.to_ascii_lowercase())
            .collect();
        let targets: Vec<String> = c
            .call_targets
            .iter()
            .filter(|t| !own.contains(&t.to_ascii_lowercase()))
            .filter(|t| !t.eq_ignore_ascii_case(address))
            .cloned()
            .collect();
        if targets.len() > policy.max_linked {
            log(format!(
                "{} hard-coded call targets; fetching the first {}",
                targets.len(),
                policy.max_linked
            ));
        }
        for t in targets.iter().take(policy.max_linked) {
            if budget.left == 0 {
                log("fetch budget spent; remaining dependencies left unfetched".into());
                break;
            }
            match fetch_inner(client, t, chain, opts, policy, depth - 1, budget, log) {
                Ok(mut lc) => {
                    lc.source = decompile::render(&lc, "Linked");
                    c.linked.push(lc);
                }
                Err(e) => log(format!("call target {}: {}", t, e)),
            }
        }
    }
    Ok(c)
}

/// Resolve the routing pattern of `c` and compose it with the code it forwards to.
fn resolve(
    client: &Client,
    c: Contract,
    code: &[u8],
    opts: &Options,
    budget: &mut Budget,
    log: &mut dyn FnMut(String),
) -> Result<Contract, String> {
    let address = c.address.clone().unwrap_or_default();
    let chain = c.chain.clone().unwrap_or_default();
    let has_selector = |sel: &str| {
        c.functions.iter().any(|f| {
            f.selector
                .as_deref()
                .is_some_and(|s| s.eq_ignore_ascii_case(sel))
        })
    };
    // A diamond: the fallback looks the facet up under the selector, or the loupe is present.
    let looks_like_diamond =
        c.diamond_lookup.is_some() || has_selector("0x7a0ed627") || has_selector("0x1f931c1c");
    if looks_like_diamond {
        if let Some(d) = rpc::resolve_diamond(client, &address, c.diamond_lookup.as_ref())? {
            log(format!(
                "EIP-2535 diamond: {} facets (from {}) — fetching...",
                d.facets.len(),
                d.source
            ));
            let mut parts = Vec::new();
            for facet in d.facets {
                if !budget.take(&facet.address) {
                    log(format!("facet {} skipped (budget)", facet.address));
                    continue;
                }
                match client.get_code(&facet.address) {
                    Ok(fc) if !fc.is_empty() => {
                        let mut pc = decompile::decompile(&fc, opts);
                        pc.address = Some(facet.address.clone());
                        pc.chain = Some(chain.clone());
                        parts.push((PartRole::Facet, facet.address, facet.selectors, pc));
                    }
                    Ok(_) => log(format!("facet {} has no code", facet.address)),
                    Err(e) => log(format!("facet {}: {}", facet.address, e)),
                }
            }
            let kind = format!("EIP-2535 diamond ({} facets)", parts.len());
            return Ok(decompile::compose(c, &kind, None, parts));
        }
    }
    // A proxy: a single implementation behind a known slot, a clone or a hard-coded target.
    let slots: Vec<U256> = c
        .delegatecall_slots
        .iter()
        .filter_map(|s| U256::from_hex_str(s))
        .collect();
    let targets: Vec<U256> = c
        .delegatecall_targets
        .iter()
        .filter_map(|s| U256::from_hex_str(s))
        .collect();
    let is_proxy = !slots.is_empty() || !targets.is_empty() || code.len() < 100;
    if !is_proxy {
        return Ok(c);
    }
    let p = match rpc::resolve_proxy(client, &address, code, &slots, &targets) {
        Ok(Some(p)) => p,
        Ok(None) => return Ok(c),
        Err(e) => {
            log(format!("proxy resolution failed: {}", e));
            return Ok(c);
        }
    };
    log(format!(
        "{}: implementation {} — fetching...",
        p.kind, p.implementation
    ));
    let mut c = c;
    c.proxy = Some(ProxyRef {
        kind: p.kind.clone(),
        implementation: p.implementation.clone(),
        admin: p.admin.clone(),
        contract: None,
    });
    if !budget.take(&p.implementation) {
        return Ok(c);
    }
    let impl_code = client.get_code(&p.implementation)?;
    if impl_code.is_empty() {
        log(format!("implementation {} has no code", p.implementation));
        return Ok(c);
    }
    let mut ic = decompile::decompile(&impl_code, opts);
    ic.address = Some(p.implementation.clone());
    ic.chain = Some(chain);
    let parts = vec![(PartRole::Implementation, p.implementation, Vec::new(), ic)];
    Ok(decompile::compose(c, &p.kind, p.admin, parts))
}
