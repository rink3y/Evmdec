//! Minimal JSON-RPC client (eth_getCode, eth_getStorageAt, eth_call, eth_chainId) with endpoint
//! Besides fetching code and storage, this module resolves proxies to their implementation and
//! EIP-2535 diamonds to their facets (through the loupe, or the reference storage layout).
//! fallback, and proxy resolution (EIP-1967, EIP-1167, beacon, storage-slot delegatecall).

use crate::decompile::DiamondLookup;
use crate::hex;
use crate::u256::U256;
use crate::{expr, keccak};
use serde_json::{json, Value};

/// A known network with the public endpoints to try when the user gives none.
#[derive(Clone, Debug)]
pub struct Chain {
    /// Short name accepted on the command line (`mainnet`, `sepolia`, ...).
    pub name: &'static str,
    /// EIP-155 chain id; also accepted in place of the name.
    pub id: u64,
    /// Public JSON-RPC URLs, tried in order until one answers.
    pub endpoints: &'static [&'static str],
}

/// Built-in networks, looked up by [`chain_by_name`].
pub const CHAINS: &[Chain] = &[
    Chain {
        name: "mainnet",
        id: 1,
        endpoints: &[
            "https://ethereum-rpc.publicnode.com",
            "https://eth.llamarpc.com",
            "https://cloudflare-eth.com",
            "https://rpc.ankr.com/eth",
        ],
    },
    Chain {
        name: "sepolia",
        id: 11155111,
        endpoints: &[
            "https://ethereum-sepolia-rpc.publicnode.com",
            "https://rpc.sepolia.org",
        ],
    },
    Chain {
        name: "arbitrum",
        id: 42161,
        endpoints: &[
            "https://arbitrum-one-rpc.publicnode.com",
            "https://arb1.arbitrum.io/rpc",
        ],
    },
    Chain {
        name: "optimism",
        id: 10,
        endpoints: &[
            "https://optimism-rpc.publicnode.com",
            "https://mainnet.optimism.io",
        ],
    },
    Chain {
        name: "base",
        id: 8453,
        endpoints: &[
            "https://base-rpc.publicnode.com",
            "https://mainnet.base.org",
        ],
    },
    Chain {
        name: "polygon",
        id: 137,
        endpoints: &[
            "https://polygon-bor-rpc.publicnode.com",
            "https://polygon-rpc.com",
        ],
    },
    Chain {
        name: "bsc",
        id: 56,
        endpoints: &[
            "https://bsc-rpc.publicnode.com",
            "https://bsc-dataseed.binance.org",
        ],
    },
    Chain {
        name: "avalanche",
        id: 43114,
        endpoints: &[
            "https://avalanche-c-chain-rpc.publicnode.com",
            "https://api.avax.network/ext/bc/C/rpc",
        ],
    },
    Chain {
        name: "gnosis",
        id: 100,
        endpoints: &[
            "https://gnosis-rpc.publicnode.com",
            "https://rpc.gnosischain.com",
        ],
    },
    Chain {
        name: "fantom",
        id: 250,
        endpoints: &["https://fantom-rpc.publicnode.com", "https://rpc.ftm.tools"],
    },
    Chain {
        name: "linea",
        id: 59144,
        endpoints: &[
            "https://linea-rpc.publicnode.com",
            "https://rpc.linea.build",
        ],
    },
    Chain {
        name: "scroll",
        id: 534352,
        endpoints: &["https://scroll-rpc.publicnode.com", "https://rpc.scroll.io"],
    },
    Chain {
        name: "blast",
        id: 81457,
        endpoints: &["https://blast-rpc.publicnode.com", "https://rpc.blast.io"],
    },
    Chain {
        name: "zksync",
        id: 324,
        endpoints: &["https://mainnet.era.zksync.io"],
    },
    Chain {
        name: "classic",
        id: 61,
        endpoints: &[
            "https://rpc.etcmc.xyz",
            "https://ethereum-classic-mainnet.gateway.tatum.io",
            "https://0xrpc.io/etc",
            "https://rpc.swiftnodes.io/rpc/etc",
            "https://lb.routeme.sh/rpc/evm/61",
            "https://geth-at.etc-network.info",
            "https://etc.rivet.link",
            "https://besu-at.etc-network.info",
            "https://etc.etcdesktop.com",
        ],
    },
];

/// Find a built-in chain by case-insensitive name or by decimal chain id.
pub fn chain_by_name(name: &str) -> Option<&'static Chain> {
    CHAINS
        .iter()
        .find(|c| c.name.eq_ignore_ascii_case(name) || c.id.to_string() == name)
}

/// JSON-RPC client that fails over across several endpoints.
#[derive(Clone, Debug)]
pub struct Client {
    /// Endpoints tried in order; the first that returns a result wins.
    pub endpoints: Vec<String>,
    /// Per-request timeout applied to each endpoint.
    pub timeout_secs: u64,
}

impl Client {
    /// Endpoints from `--rpc`, else `EVMDEC_RPC_URL` (comma-separated), else the chain's defaults.
    pub fn new(rpc: Option<&str>, chain: &str) -> Result<Client, String> {
        let mut endpoints: Vec<String> = Vec::new();
        if let Some(r) = rpc {
            endpoints.extend(
                r.split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty()),
            );
        } else if let Ok(env) = std::env::var("EVMDEC_RPC_URL") {
            endpoints.extend(
                env.split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty()),
            );
        }
        if endpoints.is_empty() {
            let c = chain_by_name(chain).ok_or_else(|| {
                format!(
                    "unknown chain '{}' (known: {})",
                    chain,
                    CHAINS.iter().map(|c| c.name).collect::<Vec<_>>().join(", ")
                )
            })?;
            endpoints.extend(c.endpoints.iter().map(|s| s.to_string()));
        }
        Ok(Client {
            endpoints,
            timeout_secs: 20,
        })
    }

    /// Send one JSON-RPC request, trying each endpoint until one returns a `result`.
    /// A JSON-RPC `error`, a transport failure or a malformed body all move on to the next
    /// endpoint; the error reported is the last one seen.
    pub fn call(&self, method: &str, params: Value) -> Result<Value, String> {
        self.call_where(method, params, |_| true)
    }

    /// Like [`Client::call`], but a `result` that `conclusive` rejects also moves on to the
    /// next endpoint: a node that is behind, pruned or on the wrong network answers "no code"
    /// or "zero" for an account that exists, and only agreement across the endpoints makes such
    /// an empty answer believable. The first accepted result wins; when every endpoint that
    /// answered gave a rejected result, the first of those is returned.
    pub fn call_where(
        &self,
        method: &str,
        params: Value,
        conclusive: impl Fn(&Value) -> bool,
    ) -> Result<Value, String> {
        let body = json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params});
        let mut last_err = String::new();
        let mut inconclusive: Option<Value> = None;
        for ep in &self.endpoints {
            let agent = ureq::AgentBuilder::new()
                .timeout(std::time::Duration::from_secs(self.timeout_secs))
                .build();
            let resp = agent
                .post(ep)
                .set("content-type", "application/json")
                .send_json(body.clone());
            match resp {
                Ok(r) => match r.into_json::<Value>() {
                    Ok(v) => {
                        if let Some(err) = v.get("error") {
                            last_err = format!("{}: {}", ep, err);
                            continue;
                        }
                        match v.get("result") {
                            Some(res) if conclusive(res) => return Ok(res.clone()),
                            Some(res) => {
                                inconclusive.get_or_insert_with(|| res.clone());
                            }
                            None => last_err = format!("{}: malformed response", ep),
                        }
                    }
                    Err(e) => last_err = format!("{}: {}", ep, e),
                },
                Err(e) => last_err = format!("{}: {}", ep, e),
            }
        }
        if let Some(v) = inconclusive {
            return Ok(v);
        }
        Err(format!(
            "all RPC endpoints failed; last error: {}",
            last_err
        ))
    }

    /// `eth_getCode` at the latest block, decoded from hex. An empty answer is accepted only
    /// when no endpoint returns code.
    pub fn get_code(&self, address: &str) -> Result<Vec<u8>, String> {
        let has_code = |v: &Value| {
            v.as_str()
                .is_some_and(|s| s.trim_start_matches("0x").len() > 1)
        };
        let v = self.call_where("eth_getCode", json!([address, "latest"]), has_code)?;
        let s = v.as_str().ok_or("eth_getCode: result is not a string")?;
        hex::decode(s)
    }

    /// `eth_getStorageAt` for a hex `slot` at the latest block. A zero answer is accepted only
    /// when no endpoint returns a value.
    pub fn get_storage(&self, address: &str, slot: &str) -> Result<U256, String> {
        let non_zero = |v: &Value| {
            v.as_str()
                .and_then(U256::from_hex_str)
                .is_some_and(|x| !x.is_zero())
        };
        let v = self.call_where(
            "eth_getStorageAt",
            json!([address, slot, "latest"]),
            non_zero,
        )?;
        let s = v
            .as_str()
            .ok_or("eth_getStorageAt: result is not a string")?;
        U256::from_hex_str(s).ok_or_else(|| format!("bad storage value {}", s))
    }

    /// `eth_call` of hex `data` against `to` at the latest block, returning the raw return data.
    pub fn eth_call(&self, to: &str, data: &str) -> Result<Vec<u8>, String> {
        let v = self.call("eth_call", json!([{"to": to, "data": data}, "latest"]))?;
        let s = v.as_str().ok_or("eth_call: result is not a string")?;
        hex::decode(s)
    }

    /// `eth_chainId`, parsed from its hex string.
    pub fn chain_id(&self) -> Result<u64, String> {
        let v = self.call("eth_chainId", json!([]))?;
        let s = v.as_str().ok_or("eth_chainId: result is not a string")?;
        u64::from_str_radix(s.trim_start_matches("0x"), 16).map_err(|e| e.to_string())
    }
}

/// Is `s` a `0x`-prefixed 20-byte hex address (surrounding whitespace ignored)?
pub fn is_address(s: &str) -> bool {
    let t = s.trim();
    t.len() == 42 && t.starts_with("0x") && t[2..].chars().all(|c| c.is_ascii_hexdigit())
}

/// Format the low 20 bytes of a word as a `0x`-prefixed address.
pub fn addr_to_string(a: U256) -> String {
    a.to_hex_padded(20)
}

/// EIP-1967 implementation slot: keccak256("eip1967.proxy.implementation") - 1.
pub const EIP1967_IMPL: &str = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc";
/// EIP-1967 beacon slot: keccak256("eip1967.proxy.beacon") - 1.
pub const EIP1967_BEACON: &str =
    "0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50";
/// EIP-1967 admin slot: keccak256("eip1967.proxy.admin") - 1.
pub const EIP1967_ADMIN: &str =
    "0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103";
/// OpenZeppelin legacy (pre-1967) implementation slot: keccak256("org.zeppelinos.proxy.implementation").
pub const ZEPPELINOS_IMPL: &str =
    "0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3";

/// A resolved proxy: which pattern matched and where the code actually lives.
#[derive(Clone, Debug, serde::Serialize)]
pub struct ProxyInfo {
    /// Human-readable pattern name, e.g. "EIP-1967 proxy" or "EIP-1167 minimal proxy".
    pub kind: String,
    /// Address of the implementation contract the proxy delegates to.
    pub implementation: String,
    /// Admin address from the EIP-1967 admin slot, when that slot is set.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub admin: Option<String>,
}

/// EIP-1167 minimal proxy: 363d3d373d3d3d363d73`<addr>`5af43d82803e903d91602b57fd5bf3 (and the
/// 0age / Solady variants, which also embed the address after `73`).
pub fn minimal_proxy_target(code: &[u8]) -> Option<String> {
    let pats: [&[u8]; 2] = [
        &[0x36, 0x3d, 0x3d, 0x37, 0x3d, 0x3d, 0x3d, 0x36, 0x3d, 0x73],
        &[
            0x36, 0x3d, 0x3d, 0x37, 0x3d, 0x3d, 0x3d, 0x36, 0x3d, 0x3d, 0x73,
        ],
    ];
    for p in pats {
        if code.len() >= p.len() + 20 && code.starts_with(p) {
            return Some(hex::encode(&code[p.len()..p.len() + 20]));
        }
    }
    // Generic: short runtime with a single PUSH20 followed by DELEGATECALL somewhere.
    if code.len() < 120 {
        let mut i = 0;
        while i < code.len() {
            let op = code[i];
            if op == 0x73 && i + 21 <= code.len() && code[i + 21..].contains(&0xf4) {
                return Some(hex::encode(&code[i + 1..i + 21]));
            }
            i += 1 + if (0x60..=0x7f).contains(&op) {
                (op - 0x5f) as usize
            } else {
                0
            };
        }
    }
    None
}

/// Try to resolve the implementation behind a proxy at `address`.
pub fn resolve_proxy(
    client: &Client,
    address: &str,
    code: &[u8],
    delegatecall_slots: &[U256],
    const_targets: &[U256],
) -> Result<Option<ProxyInfo>, String> {
    if let Some(t) = minimal_proxy_target(code) {
        return Ok(Some(ProxyInfo {
            kind: "EIP-1167 minimal proxy".into(),
            implementation: t,
            admin: None,
        }));
    }
    let nonzero = |v: U256| -> Option<String> {
        if v.is_zero() {
            None
        } else {
            Some(addr_to_string(v))
        }
    };
    if let Some(impl_) = nonzero(client.get_storage(address, EIP1967_IMPL)?) {
        let admin = nonzero(client.get_storage(address, EIP1967_ADMIN)?);
        return Ok(Some(ProxyInfo {
            kind: "EIP-1967 proxy".into(),
            implementation: impl_,
            admin,
        }));
    }
    if let Some(beacon) = nonzero(client.get_storage(address, EIP1967_BEACON)?) {
        // implementation() on the beacon
        let data = client.eth_call(&beacon, "0x5c60da1b")?;
        if data.len() >= 32 {
            let impl_ = U256::from_be_bytes(&data[..32]);
            if !impl_.is_zero() {
                return Ok(Some(ProxyInfo {
                    kind: format!("EIP-1967 beacon proxy (beacon {})", beacon),
                    implementation: addr_to_string(impl_),
                    admin: None,
                }));
            }
        }
    }
    if let Some(impl_) = nonzero(client.get_storage(address, ZEPPELINOS_IMPL)?) {
        return Ok(Some(ProxyInfo {
            kind: "ZeppelinOS proxy".into(),
            implementation: impl_,
            admin: None,
        }));
    }
    // Storage slots used as delegatecall targets in the code.
    for slot in delegatecall_slots {
        let v = client.get_storage(address, &slot.to_hex_padded(32))?;
        let a = v & crate::expr::mask_bits(160);
        if !a.is_zero() {
            return Ok(Some(ProxyInfo {
                kind: format!("proxy (implementation in storage slot {})", slot.to_hex()),
                implementation: addr_to_string(a),
                admin: None,
            }));
        }
    }
    if let Some(t) = const_targets.first() {
        return Ok(Some(ProxyInfo {
            kind: "proxy (hard-coded implementation)".into(),
            implementation: addr_to_string(*t),
            admin: None,
        }));
    }
    Ok(None)
}

/// One facet of a diamond with the selectors routed to it.
#[derive(Clone, Debug, serde::Serialize)]
pub struct Facet {
    /// Facet address.
    pub address: String,
    /// Selectors routed to it, as `0x`-prefixed 4-byte hex.
    pub selectors: Vec<String>,
}

/// A resolved EIP-2535 diamond: its facets and how they were found.
#[derive(Clone, Debug, serde::Serialize)]
pub struct DiamondInfo {
    /// The facets, in the order the diamond lists them.
    pub facets: Vec<Facet>,
    /// `loupe` when read through `IDiamondLoupe`, `storage` when read from the reference
    /// layout of the diamond storage struct.
    pub source: &'static str,
}

/// `facets()` of `IDiamondLoupe`.
pub(crate) const SEL_FACETS: &str = "0x7a0ed627";
/// `diamondCut((address,uint8,bytes4[])[],address,bytes)` of `IDiamondCut`.
pub(crate) const SEL_DIAMOND_CUT: &str = "0x1f931c1c";
/// `facetAddresses()` of `IDiamondLoupe`.
const SEL_FACET_ADDRESSES: &str = "0x52ef6b2c";
/// `facetFunctionSelectors(address)` of `IDiamondLoupe`.
const SEL_FACET_SELECTORS: &str = "0xadfca15e";
/// Facets read at most, a bound on a hostile or broken loupe.
const MAX_FACETS: usize = 128;

/// Resolve the facets of the diamond at `address`: through the loupe when the diamond has one,
/// else from storage when `lookup` names the selector mapping of the reference layout
/// (`selectorToFacetAndPosition` at the diamond storage position, `facetFunctionSelectors` one
/// slot further and `facetAddresses` two slots further). `None` when neither works.
pub fn resolve_diamond(
    client: &Client,
    address: &str,
    lookup: Option<&DiamondLookup>,
) -> Result<Option<DiamondInfo>, String> {
    if let Some(facets) = loupe_facets(client, address) {
        return Ok(Some(DiamondInfo {
            facets,
            source: "loupe",
        }));
    }
    if let Some(facets) = loupe_facets_by_address(client, address) {
        return Ok(Some(DiamondInfo {
            facets,
            source: "loupe",
        }));
    }
    let Some(lookup) = lookup else {
        return Ok(None);
    };
    let Some(root) = U256::from_hex_str(&lookup.slot) else {
        return Ok(None);
    };
    let facets = storage_facets(client, address, root)?;
    Ok((!facets.is_empty()).then_some(DiamondInfo {
        facets,
        source: "storage",
    }))
}

/// `facets()`: `(address facetAddress, bytes4[] functionSelectors)[]`.
fn loupe_facets(client: &Client, address: &str) -> Option<Vec<Facet>> {
    let data = client.eth_call(address, SEL_FACETS).ok()?;
    let r = AbiReader::new(&data);
    let array = r.offset(0)?;
    let n = r.word(array)?.as_usize()?;
    if n == 0 || n > MAX_FACETS {
        return None;
    }
    let mut facets = Vec::with_capacity(n);
    for i in 0..n {
        let tuple = r.offset_from(array + 32, array + 32 + 32 * i)?;
        let facet = r.word(tuple)?;
        let sels = r.offset_from(tuple, tuple + 32)?;
        let selectors = r.selectors(sels)?;
        facets.push(Facet {
            address: addr_to_string(facet & expr::mask_bits(160)),
            selectors,
        });
    }
    Some(facets)
}

/// `facetAddresses()` then `facetFunctionSelectors(address)` for each, for a loupe whose
/// `facets()` is missing or fails.
fn loupe_facets_by_address(client: &Client, address: &str) -> Option<Vec<Facet>> {
    let data = client.eth_call(address, SEL_FACET_ADDRESSES).ok()?;
    let r = AbiReader::new(&data);
    let array = r.offset(0)?;
    let n = r.word(array)?.as_usize()?;
    if n == 0 || n > MAX_FACETS {
        return None;
    }
    let mut facets = Vec::with_capacity(n);
    for i in 0..n {
        let facet = addr_to_string(r.word(array + 32 + 32 * i)? & crate::expr::mask_bits(160));
        let arg = format!(
            "{}{:0>64}",
            SEL_FACET_SELECTORS,
            facet.trim_start_matches("0x")
        );
        let data = client.eth_call(address, &arg).ok()?;
        let rr = AbiReader::new(&data);
        let sels = rr.offset(0)?;
        let selectors = rr.selectors(sels)?;
        facets.push(Facet {
            address: facet,
            selectors,
        });
    }
    Some(facets)
}

/// Facets from the reference diamond storage layout rooted at `root`.
fn storage_facets(client: &Client, address: &str, root: U256) -> Result<Vec<Facet>, String> {
    let slot = |k: U256| k.to_hex_padded(32);
    let addresses_len = client
        .get_storage(address, &slot(root + U256::from_u64(2)))?
        .as_usize()
        .unwrap_or(0);
    if addresses_len == 0 || addresses_len > MAX_FACETS {
        return Ok(Vec::new());
    }
    let addresses_data = U256::from_be_bytes(&keccak::keccak256(
        &(root + U256::from_u64(2)).to_be_bytes(),
    ));
    let mut facets = Vec::new();
    for i in 0..addresses_len {
        let facet = client
            .get_storage(address, &slot(addresses_data + U256::from_u64(i as u64)))?
            & crate::expr::mask_bits(160);
        if facet.is_zero() {
            continue;
        }
        // facetFunctionSelectors[facet].functionSelectors: a bytes4[] at the entry's first slot.
        let mut pre = Vec::with_capacity(64);
        pre.extend_from_slice(&facet.to_be_bytes());
        pre.extend_from_slice(&(root + U256::ONE).to_be_bytes());
        let entry = U256::from_be_bytes(&keccak::keccak256(&pre));
        let n = client
            .get_storage(address, &slot(entry))?
            .as_usize()
            .unwrap_or(0)
            .min(4096);
        let data = U256::from_be_bytes(&keccak::keccak256(&entry.to_be_bytes()));
        let mut selectors = Vec::with_capacity(n);
        let mut word = U256::ZERO;
        for j in 0..n {
            if j % 8 == 0 {
                word = client.get_storage(address, &slot(data + U256::from_u64((j / 8) as u64)))?;
            }
            // `bytes4` elements pack eight to a slot from the low-order end.
            let bytes = word.to_be_bytes();
            let lo = 32 - 4 * (j % 8 + 1);
            selectors.push(format!(
                "0x{}",
                hex::encode(&bytes[lo..lo + 4]).trim_start_matches("0x")
            ));
        }
        facets.push(Facet {
            address: addr_to_string(facet),
            selectors,
        });
    }
    Ok(facets)
}

/// A bounds-checked reader over ABI-encoded return data.
struct AbiReader<'a> {
    data: &'a [u8],
}

impl<'a> AbiReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        AbiReader { data }
    }

    /// The 32-byte word at byte offset `at`.
    fn word(&self, at: usize) -> Option<U256> {
        let end = at.checked_add(32)?;
        (end <= self.data.len()).then(|| U256::from_be_bytes(&self.data[at..end]))
    }

    /// The offset word at `at`, as an absolute position.
    fn offset(&self, at: usize) -> Option<usize> {
        self.offset_from(0, at)
    }

    /// The offset word at `at`, relative to `base`, as an absolute position inside the data.
    fn offset_from(&self, base: usize, at: usize) -> Option<usize> {
        let off = base.checked_add(self.word(at)?.as_usize()?)?;
        (off < self.data.len()).then_some(off)
    }

    /// A `bytes4[]` whose length word sits at `at`.
    fn selectors(&self, at: usize) -> Option<Vec<String>> {
        let n = self.word(at)?.as_usize()?;
        if n > 4096 {
            return None;
        }
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let w = self.word(at + 32 + 32 * i)?.to_be_bytes();
            out.push(format!(
                "0x{}",
                hex::encode(&w[..4]).trim_start_matches("0x")
            ));
        }
        Some(out)
    }
}
