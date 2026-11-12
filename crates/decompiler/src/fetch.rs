//! Fetching a contract by address and assembling what it really is.
//!
//! A contract's code is rarely the whole story: a proxy forwards to an implementation, a
//! diamond routes each selector to a facet, and all of them call other contracts whose
//! behaviour is part of theirs. This module fetches the code at an address, resolves the
//! pattern it implements, fetches the code it forwards to and composes the pieces into one
//! [`Contract`] ([`crate::decompile::compose`]) so the analyzer sees what callers see.
//!
//! It then walks the call graph from there. Level by level, every call target of the contracts
//! fetched so far (a fixed address, a library, the address a storage slot holds) is fetched and
//! resolved the same way, libraries and targets whose state a call may change first, targets
//! that are only read last. The walk ends at the configured depth, at the limit on contracts per
//! request, or when its time is up, and what it saw without fetching is listed with the reason.
//! Finally each fetched contract's own storage is asked whether it approves the contracts that
//! call it, at the slots and mapping entries its access checks read.

use crate::analyze;
use crate::clock;
use crate::decompile::{self, Contract, Link, Options, PartInput, PartRole, ProxyRef, Unfollowed};
use crate::expr;
use crate::keccak;
use crate::rpc::{self, Client};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

/// What to fetch beyond the code at the address.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {
    /// Resolve proxies and diamonds and compose them with their code.
    pub follow: bool,
    /// Call targets fetched from one contract, at most.
    pub max_linked: usize,
    /// Code units fetched for one request, at most, across parts and dependencies.
    pub max_total: usize,
    /// Call edges to follow from the contract asked for: 1 fetches what it calls, 2 also what
    /// those contracts call, and so on. 0 fetches no dependency.
    pub depth: usize,
    /// Time one dependency may take to decompile before it is left out.
    pub contract_time: Duration,
    /// Time the walk over dependencies may take before it stops fetching.
    pub walk_time: Duration,
}

impl Default for Policy {
    fn default() -> Self {
        Policy {
            follow: true,
            max_linked: 8,
            max_total: 40,
            depth: 2,
            contract_time: Duration::from_secs(20),
            walk_time: Duration::from_secs(120),
        }
    }
}

/// Gate locations read per contract when asking whom it approves, at most.
const MAX_GATES_READ: usize = 8;
/// Calling contracts checked against one contract's gates, at most.
const MAX_CALLERS_CHECKED: usize = 4;

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
    let opts = &Options {
        embedded: true,
        ..opts.clone()
    };
    let mut fetcher = Fetcher {
        client,
        chain,
        opts,
        policy,
        cache,
        log,
        seen: HashSet::new(),
        left: policy.max_total,
        decompiled: HashMap::new(),
        time: None,
        calls: Vec::new(),
    };
    let root = fetcher.one(address)?;
    if !policy.follow || policy.depth == 0 {
        return Ok(root);
    }
    Ok(fetcher.walk(root))
}

/// A call target waiting to be fetched.
struct Edge {
    /// Address of the target.
    target: String,
    /// Address of the contract that calls it.
    from: String,
    /// How the caller names it.
    how: String,
    /// Fetch order: libraries, then targets a call may change, then targets only read.
    class: u8,
}

/// A storage slot as short hex, for messages: `0x5` rather than 32 bytes.
fn short_slot(slot: &str) -> String {
    let digits = slot.trim_start_matches("0x").trim_start_matches('0');
    format!("0x{}", if digits.is_empty() { "0" } else { digits })
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
    /// Decompilations by code hash: the same code at a second address is decompiled once.
    decompiled: HashMap<[u8; 32], Contract>,
    /// The time one decompilation may take; unlimited for the contract asked for.
    time: Option<Duration>,
    /// Call edges seen so far, fetched or not: `(caller, target)`, lower-case.
    calls: Vec<(String, String)>,
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

    /// Decompile `code`, reusing the result for code seen before. `None` when it took longer
    /// than the time a dependency is given.
    fn decompile(&mut self, code: &[u8]) -> Option<Contract> {
        let hash = keccak::keccak256(code);
        if let Some(known) = self.decompiled.get(&hash) {
            return Some(known.clone());
        }
        let opts = self.opts;
        let c = match self.time {
            Some(time) => clock::run(time, || decompile::decompile(code, opts))?,
            None => decompile::decompile(code, opts),
        };
        self.decompiled.insert(hash, c.clone());
        Some(c)
    }

    /// Fetch the code at `address`, decompile it and resolve the proxy or diamond it is.
    fn one(&mut self, address: &str) -> Result<Contract, String> {
        if !self.take(address) {
            return Err("already fetched in this request, or the fetch limit is reached".into());
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
        let Some(mut c) = self.decompile(&code) else {
            return Err(self.too_slow());
        };
        c.address = Some(address.to_string());
        c.chain = Some(self.chain.to_string());
        if !self.policy.follow {
            return Ok(c);
        }
        Ok(self.resolve(c, address, &code))
    }

    /// The reason given for a dependency whose decompilation was abandoned.
    fn too_slow(&self) -> String {
        format!(
            "decompiling it took longer than {} s",
            self.time.unwrap_or_default().as_secs()
        )
    }

    /// The call targets of `c`, with the slots that hold one read from the chain (and recorded
    /// in `c.stored_targets`), and the slots that hold none.
    fn edges(&mut self, c: &mut Contract) -> (Vec<Edge>, Vec<Unfollowed>) {
        let from = c.address.clone().unwrap_or_default();
        let mut edges: Vec<Edge> = Vec::new();
        let mut empty: Vec<Unfollowed> = Vec::new();
        let class_of = |c: &Contract, key: &str| match c.written_targets.iter().any(|w| w == key) {
            true => 1,
            false => 2,
        };
        for library in &c.library_targets {
            edges.push(Edge {
                target: library.clone(),
                from: from.clone(),
                how: "library, run in the caller's storage".into(),
                class: 0,
            });
        }
        for target in &c.clone_targets {
            edges.push(Edge {
                target: target.clone(),
                from: from.clone(),
                how: "code run by the clones the caller creates".into(),
                class: 0,
            });
        }
        for target in &c.call_targets {
            edges.push(Edge {
                target: target.clone(),
                from: from.clone(),
                how: "fixed address in the code".into(),
                class: class_of(c, target),
            });
        }
        for slot in c.call_target_slots.clone() {
            match self.client.get_storage(&from, &slot) {
                Ok(v) => {
                    let a = v & expr::mask_bits(160);
                    if a.is_zero() {
                        empty.push(Unfollowed {
                            target: format!("slot {}", short_slot(&slot)),
                            from: from.clone(),
                            reason: "the slot holds no address".into(),
                        });
                        continue;
                    }
                    let target = rpc::addr_to_string(a);
                    c.stored_targets.push((slot.clone(), target.clone()));
                    edges.push(Edge {
                        target,
                        from: from.clone(),
                        how: format!("address held in slot {}", short_slot(&slot)),
                        class: class_of(c, &slot),
                    });
                }
                Err(e) => empty.push(Unfollowed {
                    target: format!("slot {}", short_slot(&slot)),
                    from: from.clone(),
                    reason: format!("the slot could not be read: {e}"),
                }),
            }
        }
        let own: Vec<String> = c
            .parts
            .iter()
            .map(|p| p.address.to_ascii_lowercase())
            .collect();
        edges.retain(|e| {
            let target = e.target.to_ascii_lowercase();
            !own.contains(&target) && !target.eq_ignore_ascii_case(&from)
        });
        for e in &edges {
            let call = (from.to_ascii_lowercase(), e.target.to_ascii_lowercase());
            if !self.calls.contains(&call) {
                self.calls.push(call);
            }
        }
        for created in &c.embedded {
            for library in &created.library_targets {
                edges.push(Edge {
                    target: library.clone(),
                    from: from.clone(),
                    how: "library of a contract the caller creates".into(),
                    class: 0,
                });
            }
            for target in &created.call_targets {
                edges.push(Edge {
                    target: target.clone(),
                    from: from.clone(),
                    how: "fixed address in a contract the caller creates".into(),
                    class: class_of(created, target),
                });
            }
        }
        (edges, empty)
    }

    /// Walk the call graph from `root`, level by level, and return it with every contract
    /// reached in `linked` and every target left out in `unfollowed`.
    fn walk(&mut self, root: Contract) -> Contract {
        let started = Instant::now();
        let policy = self.policy;
        let mut all: Vec<Contract> = vec![root];
        let mut level: Vec<usize> = vec![0];
        let mut unfollowed: Vec<Unfollowed> = Vec::new();
        self.time = Some(policy.contract_time);
        for depth in 1..=policy.depth {
            let mut edges: Vec<Edge> = Vec::new();
            for i in level.drain(..) {
                let (found, empty) = self.edges(&mut all[i]);
                edges.extend(found);
                unfollowed.extend(empty);
            }
            edges.sort_by_key(|e| e.class);
            let mut fetched_from: HashMap<String, usize> = HashMap::new();
            for e in edges {
                if self.seen.contains(&e.target.to_ascii_lowercase()) {
                    continue;
                }
                let from_this = fetched_from.entry(e.from.clone()).or_insert(0);
                let reason = if self.left == 0 {
                    Some(format!(
                        "the limit of {} contracts per request was reached",
                        policy.max_total
                    ))
                } else if started.elapsed() > policy.walk_time {
                    Some(format!(
                        "the walk over dependencies had run for {} s",
                        policy.walk_time.as_secs()
                    ))
                } else if *from_this >= policy.max_linked {
                    Some(format!(
                        "{} targets of this contract were fetched already",
                        policy.max_linked
                    ))
                } else {
                    None
                };
                let outcome = match reason {
                    Some(reason) => Err(reason),
                    None => self.one(&e.target),
                };
                match outcome {
                    Ok(mut lc) => {
                        *from_this += 1;
                        lc.link = Some(Link {
                            from: e.from,
                            how: e.how,
                            depth,
                        });
                        level.push(all.len());
                        all.push(lc);
                    }
                    Err(reason) => {
                        (self.log)(&format!("call target {}: {}", e.target, reason));
                        unfollowed.push(Unfollowed {
                            target: e.target,
                            from: e.from,
                            reason,
                        });
                    }
                }
            }
            if level.is_empty() {
                break;
            }
        }
        for i in level {
            let c = &all[i];
            let from = c.address.clone().unwrap_or_default();
            let fixed = c.library_targets.iter().chain(&c.call_targets).cloned();
            let held = c
                .call_target_slots
                .iter()
                .map(|slot| format!("slot {}", short_slot(slot)));
            for target in fixed.chain(held) {
                if self.seen.contains(&target.to_ascii_lowercase()) {
                    continue;
                }
                unfollowed.push(Unfollowed {
                    target,
                    from: from.clone(),
                    reason: format!(
                        "it is more than {} call edges from the contract asked for",
                        policy.depth
                    ),
                });
            }
        }
        self.read_gates(&mut all);
        let mut contracts = all.into_iter();
        let mut root = contracts.next().expect("the walk starts from the root");
        for mut lc in contracts {
            lc.source = decompile::render(&lc, "Linked");
            root.linked.push(lc);
        }
        root.unfollowed = unfollowed;
        root
    }

    /// Ask each contract's storage whether it approves the contracts that call it: at the slots
    /// its access checks compare `msg.sender` with, and at the mapping entries they test under
    /// `msg.sender`.
    fn read_gates(&mut self, all: &mut [Contract]) {
        for c in all.iter_mut() {
            let Some(address) = c.address.clone() else {
                continue;
            };
            let callers: Vec<String> = self
                .calls
                .iter()
                .filter(|(_, to)| to.eq_ignore_ascii_case(&address))
                .map(|(from, _)| from.clone())
                .take(MAX_CALLERS_CHECKED)
                .collect();
            if callers.is_empty() {
                continue;
            }
            let gates = analyze::gates(c);
            if gates.slots.is_empty() && gates.keys.is_empty() {
                continue;
            }
            let mut read = true;
            let admit = |caller: &str, admits: &mut Vec<String>| {
                if !admits.iter().any(|a| a.eq_ignore_ascii_case(caller)) {
                    admits.push(caller.to_string());
                }
            };
            for slot in gates.slots.iter().take(MAX_GATES_READ) {
                match self.client.get_storage(&address, &slot.to_hex_padded(32)) {
                    Ok(v) => {
                        let held = rpc::addr_to_string(v & expr::mask_bits(160));
                        for caller in callers.iter().filter(|a| a.eq_ignore_ascii_case(&held)) {
                            admit(caller, &mut c.admits);
                        }
                    }
                    Err(_) => read = false,
                }
            }
            for key in gates.keys.iter().take(MAX_GATES_READ) {
                for caller in &callers {
                    let slot = U256::from_hex_str(caller).and_then(|a| analyze::key_for(*key, a));
                    let Some(slot) = slot else {
                        read = false;
                        continue;
                    };
                    match self.client.get_storage(&address, &slot.to_hex_padded(32)) {
                        Ok(v) if !v.is_zero() => admit(caller, &mut c.admits),
                        Ok(_) => {}
                        Err(_) => read = false,
                    }
                }
            }
            c.gates_read = read;
            if !c.admits.is_empty() {
                (self.log)(&format!(
                    "{} approves {} as a caller",
                    address,
                    c.admits.join(", ")
                ));
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
                    let Some(mut facet_contract) = self.decompile(&fc) else {
                        let reason = self.too_slow();
                        (self.log)(&format!("facet {}: {}", facet.address, reason));
                        continue;
                    };
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
        let Some(mut ic) = self.decompile(&impl_code) else {
            let reason = self.too_slow();
            (self.log)(&format!("implementation {}: {}", p.implementation, reason));
            return c;
        };
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
