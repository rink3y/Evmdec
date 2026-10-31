//! Minimal JSON-RPC client (eth_getCode, eth_getStorageAt, eth_call, eth_chainId) with endpoint
//! fallback, and proxy resolution (EIP-1967, EIP-1167, beacon, storage-slot delegatecall).

use crate::hex;
use crate::u256::U256;
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
            "https://etc.etcdesktop.com",
            "https://etc.rivet.link",
            "https://besu-at.etc-network.info",
            "https://0xrpc.io/etc",
            "https://rpc.etcmc.xyz",
            "https://rpc.swiftnodes.io/rpc/etc",
            "https://lb.routeme.sh/rpc/evm/61",
            "https://geth-at.etc-network.info",
            "https://ethereum-classic-mainnet.gateway.tatum.io",
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
        let body = json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params});
        let mut last_err = String::new();
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
                        if let Some(res) = v.get("result") {
                            return Ok(res.clone());
                        }
                        last_err = format!("{}: malformed response", ep);
                    }
                    Err(e) => last_err = format!("{}: {}", ep, e),
                },
                Err(e) => last_err = format!("{}: {}", ep, e),
            }
        }
        Err(format!(
            "all RPC endpoints failed; last error: {}",
            last_err
        ))
    }

    /// `eth_getCode` at the latest block, decoded from hex.
    pub fn get_code(&self, address: &str) -> Result<Vec<u8>, String> {
        let v = self.call("eth_getCode", json!([address, "latest"]))?;
        let s = v.as_str().ok_or("eth_getCode: result is not a string")?;
        hex::decode(s)
    }

    /// `eth_getStorageAt` for a hex `slot` at the latest block.
    pub fn get_storage(&self, address: &str, slot: &str) -> Result<U256, String> {
        let v = self.call("eth_getStorageAt", json!([address, slot, "latest"]))?;
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
