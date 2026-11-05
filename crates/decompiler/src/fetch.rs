//! Fetching a contract by address and assembling what it really is.
//!
//! A contract's code is rarely the whole story: a proxy forwards to an implementation, a
//! diamond routes each selector to a facet, and both call fixed addresses whose behaviour is
//! part of the contract's. This module fetches the code at an address, resolves the pattern it
//! implements, fetches the code it forwards to and composes the pieces into one
//! [`Contract`] ([`crate::decompile::compose`]) so the analyzer sees what callers see. It then
//! fetches the hard-coded dependencies and resolves each the same way, one level deep, so a
//! dependency that is itself a proxy appears as its implementation.

use crate::decompile::{self, Contract, Options, PartInput, PartRole, ProxyRef};
use crate::expr;
use crate::rpc::{self, Client};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

/// What to fetch beyond the code at the address.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

/// Code already fetched, by lower-case address, so a second pass over the same request (for
/// instance after an online signature lookup) decompiles again without asking the node again.
pub type CodeCache = HashMap<String, Vec<u8>>;

/// Fetch, resolve and compose the contract at `address` on `chain`. Progress lines go to
/// `log`; the result is the composed contract with its dependencies in `linked`.
pub fn fetch(
    client: &Client,
    address: &str,
    chain: &str,
    opts: &Options,
    policy: Policy,
    cache: &mut CodeCache,
    log: &mut dyn FnMut(&str),
) -> Result<Contract, String> {
    let mut fetcher = Fetcher {
        client,
        chain,
        opts,
        policy,
        cache,
        log,
        seen: HashSet::new(),
        left: policy.max_total,
    };
    fetcher.fetch(address, policy.depth)
}

/// One request's fetching state: the connection and options it runs with, and what it may
/// still fetch.
struct Fetcher<'a> {
    client: &'a Client,
    chain: &'a str,
    opts: &'a Options,
    policy: Policy,
    cache: &'a mut CodeCache,
    log: &'a mut dyn FnMut(&str),
    /// Addresses already fetched in this request (lower-case).
    seen: HashSet<String>,
    /// Code units left to fetch.
    left: usize,
}

impl Fetcher<'_> {
    /// Claim a fetch of `address`; `false` when it was fetched already in this request or
    /// nothing is left.
    fn take(&mut self, address: &str) -> bool {
        if self.left == 0 || !self.seen.insert(address.to_ascii_lowercase()) {
            return false;
        }
        self.left -= 1;
        true
    }

    /// The code at `address`, from the cache when this request saw it before.
    fn code(&mut self, address: &str) -> Result<Vec<u8>, String> {
        let key = address.to_ascii_lowercase();
        if let Some(code) = self.cache.get(&key) {
            return Ok(code.clone());
        }
        let code = self.client.get_code(address)?;
        self.cache.insert(key, code.clone());
        Ok(code)
    }

    fn fetch(&mut self, address: &str, depth: usize) -> Result<Contract, String> {
        if !self.take(address) {
            return Err(format!(
                "{} already fetched in this request, or the fetch budget is spent",
                address
            ));
        }
        (self.log)(&format!(
            "fetching code of {} on {}...",
            address, self.chain
        ));
        let code = self.code(address)?;
        if code.is_empty() {
            return Err(format!(
                "{} has no code on {} (not a contract, or wrong chain)",
                address, self.chain
            ));
        }
        let mut c = decompile::decompile(&code, self.opts);
        c.address = Some(address.to_string());
        c.chain = Some(self.chain.to_string());
        if !self.policy.follow {
            return Ok(c);
        }
        c = self.resolve(c, address, &code);
        if depth > 0 {
            self.link(&mut c, address, depth - 1);
        }
        Ok(c)
    }

    /// Fetch the call targets of `c` (every part's hard-coded ones, then the ones held in
    /// storage, read from the chain) into `c.linked`.
    fn link(&mut self, c: &mut Contract, address: &str, depth: usize) {
        let own: Vec<String> = c
            .parts
            .iter()
            .map(|p| p.address.to_ascii_lowercase())
            .collect();
        let mut targets: Vec<String> = c.call_targets.clone();
        for slot in c.call_target_slots.clone() {
            match self.client.get_storage(address, &slot) {
                Ok(v) => {
                    let a = v & expr::mask_bits(160);
                    if !a.is_zero() {
                        let t = rpc::addr_to_string(a);
                        c.stored_targets.push((slot, t.clone()));
                        if !targets.iter().any(|x| x.eq_ignore_ascii_case(&t)) {
                            targets.push(t);
                        }
                    }
                }
                Err(e) => (self.log)(&format!("slot {}: {}", slot, e)),
            }
        }
        let targets: Vec<String> = targets
            .into_iter()
            .filter(|t| !own.contains(&t.to_ascii_lowercase()))
            .filter(|t| !t.eq_ignore_ascii_case(address))
            .collect();
        if targets.len() > self.policy.max_linked {
            (self.log)(&format!(
                "{} hard-coded call targets; fetching the first {}",
                targets.len(),
                self.policy.max_linked
            ));
        }
        for t in targets.iter().take(self.policy.max_linked) {
            if self.left == 0 {
                (self.log)("fetch budget spent; remaining dependencies left unfetched");
                break;
            }
            match self.fetch(t, depth) {
                Ok(mut lc) => {
                    lc.source = decompile::render(&lc, "Linked");
                    c.linked.push(lc);
                }
                Err(e) => (self.log)(&format!("call target {}: {}", t, e)),
            }
        }
    }

    /// Resolve the routing pattern of `c` and compose it with the code it forwards to. A
    /// resolution that fails leaves `c` as the plain decompilation of the shell.
    fn resolve(&mut self, c: Contract, address: &str, code: &[u8]) -> Contract {
        let has_selector = |sel: &str| {
            c.functions.iter().any(|f| {
                f.selector
                    .as_deref()
                    .is_some_and(|s| s.eq_ignore_ascii_case(sel))
            })
        };
        // A diamond: the fallback looks the facet up under the selector, or the loupe or cut
        // function is present.
        let looks_like_diamond = c.diamond_lookup.is_some()
            || has_selector(rpc::SEL_FACETS)
            || has_selector(rpc::SEL_DIAMOND_CUT);
        if looks_like_diamond {
            match rpc::resolve_diamond(self.client, address, c.diamond_lookup.as_ref()) {
                Ok(Some(d)) => return self.compose_diamond(c, d),
                Ok(None) => {}
                Err(e) => (self.log)(&format!("diamond resolution failed: {}", e)),
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
            return c;
        }
        match rpc::resolve_proxy(self.client, address, code, &slots, &targets) {
            Ok(Some(p)) => self.compose_proxy(c, p),
            Ok(None) => c,
            Err(e) => {
                (self.log)(&format!("proxy resolution failed: {}", e));
                c
            }
        }
    }

    /// Fetch every facet of `d` and compose it with the shell `c`.
    fn compose_diamond(&mut self, c: Contract, d: rpc::DiamondInfo) -> Contract {
        (self.log)(&format!(
            "EIP-2535 diamond: {} facets (from {}) — fetching...",
            d.facets.len(),
            d.source
        ));
        let mut parts = Vec::new();
        for facet in d.facets {
            if !self.take(&facet.address) {
                (self.log)(&format!("facet {} skipped (budget)", facet.address));
                continue;
            }
            match self.code(&facet.address) {
                Ok(fc) if !fc.is_empty() => {
                    let mut facet_contract = decompile::decompile(&fc, self.opts);
                    facet_contract.address = Some(facet.address.clone());
                    facet_contract.chain = Some(self.chain.to_string());
                    parts.push(PartInput {
                        role: PartRole::Facet,
                        address: facet.address,
                        selectors: facet.selectors,
                        contract: facet_contract,
                    });
                }
                Ok(_) => (self.log)(&format!("facet {} has no code", facet.address)),
                Err(e) => (self.log)(&format!("facet {}: {}", facet.address, e)),
            }
        }
        let kind = format!("EIP-2535 diamond ({} facets)", parts.len());
        decompile::compose(c, &kind, None, parts)
    }

    /// Fetch the implementation behind the proxy `p` and compose it with the shell `c`.
    fn compose_proxy(&mut self, mut c: Contract, p: rpc::ProxyInfo) -> Contract {
        (self.log)(&format!(
            "{}: implementation {} — fetching...",
            p.kind, p.implementation
        ));
        c.proxy = Some(ProxyRef {
            kind: p.kind.clone(),
            implementation: p.implementation.clone(),
            admin: p.admin.clone(),
            contract: None,
        });
        if !self.take(&p.implementation) {
            return c;
        }
        let impl_code = match self.code(&p.implementation) {
            Ok(code) if !code.is_empty() => code,
            Ok(_) => {
                (self.log)(&format!("implementation {} has no code", p.implementation));
                return c;
            }
            Err(e) => {
                (self.log)(&format!("implementation {}: {}", p.implementation, e));
                return c;
            }
        };
        let mut ic = decompile::decompile(&impl_code, self.opts);
        ic.address = Some(p.implementation.clone());
        ic.chain = Some(self.chain.to_string());
        let parts = vec![PartInput {
            role: PartRole::Implementation,
            address: p.implementation,
            selectors: Vec::new(),
            contract: ic,
        }];
        decompile::compose(c, &p.kind, p.admin, parts)
    }
}
