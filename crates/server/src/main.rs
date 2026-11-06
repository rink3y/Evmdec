//! evmdec web service: decompile by address or bytecode, serve the single-page UI.

use axum::extract::{Path, State};
use axum::http::{header, StatusCode};
use axum::response::{Html, IntoResponse};
use axum::routing::{get, post};
use axum::{Json, Router};
use evmdec::decompile::{Contract, Options};
use evmdec::fetch::{CodeCache, Policy};
use evmdec::rpc::Client;
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

const INDEX: &str = include_str!("../static/index.html");
const OG_PNG: &[u8] = include_bytes!("../static/og.png");
const FAVICON: &str = include_str!("../static/favicon.svg");

#[derive(Clone, Default)]
struct AppState {
    cache: Arc<Mutex<HashMap<String, Arc<Value>>>>,
}

#[derive(Deserialize, Default)]
struct DecompileReq {
    bytecode: Option<String>,
    address: Option<String>,
    chain: Option<String>,
    rpc: Option<String>,
    #[serde(default)]
    no_follow_proxy: bool,
    /// Resolve unknown selectors online.
    #[serde(default)]
    lookup: bool,
}

fn error(status: StatusCode, msg: impl Into<String>) -> axum::response::Response {
    (status, Json(json!({"error": msg.into()}))).into_response()
}

/// Selectors of `c` and its parts that have no known signature, for an online lookup.
fn unknown_selectors(c: &Contract) -> Vec<u32> {
    c.functions
        .iter()
        .filter(|f| f.signature.is_none())
        .filter_map(|f| f.selector.as_ref())
        .filter_map(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .collect()
}

/// Whether unknown selectors are looked up online.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lookup {
    /// The built-in dictionary only.
    Offline,
    /// Ask openchain.xyz and 4byte.directory, then decompile again with what they return.
    Online,
}

/// What a request decompiles: pasted bytecode, or the contract at an address.
enum Source<'a> {
    /// Bytecode as given.
    Bytecode(&'a [u8]),
    /// The contract at `address` on `chain`, fetched under `policy` through `rpc` (or the
    /// chain's public endpoints).
    Address {
        address: &'a str,
        chain: &'a str,
        rpc: Option<&'a str>,
        policy: Policy,
    },
}

impl Source<'_> {
    /// The address shown in titles.
    fn title(&self) -> &str {
        match self {
            Source::Bytecode(_) => "bytecode",
            Source::Address { address, .. } => address,
        }
    }

    /// Decompile, resolving and composing the contract at an address. `cache` keeps the code
    /// fetched so a second pass does not ask the node again.
    fn obtain(&self, opts: &Options, cache: &mut CodeCache) -> Result<Contract, String> {
        match self {
            Source::Bytecode(code) => Ok(evmdec::decompile::decompile(code, opts)),
            Source::Address {
                address,
                chain,
                rpc,
                policy,
            } => {
                let client = Client::new(*rpc, chain)?;
                evmdec::fetch::fetch(&client, address, chain, opts, *policy, cache, &mut |_| {})
            }
        }
    }
}

/// Run the decompiler and analyzer; returns the JSON document the UI consumes.
fn run(source: &Source<'_>, lookup: Lookup) -> Result<Value, String> {
    let mut opts = Options::default();
    let mut cache = CodeCache::new();
    let mut c = source.obtain(&opts, &mut cache)?;
    if lookup == Lookup::Online {
        let sels = unknown_selectors(&c);
        if !sels.is_empty() {
            opts.extra_sigs = evmdec::sigs::lookup_online(&sels);
            if !opts.extra_sigs.is_empty() {
                c = source.obtain(&opts, &mut cache)?;
            }
        }
    }
    let r = evmdec::analyze::analyze(&c);
    let md = evmdec::analyze::render_markdown(&c, &r, source.title());
    let disasm: Vec<String> = evmdec::disasm::disassemble(&c.info.runtime)
        .iter()
        .map(evmdec::disasm::format_instruction)
        .collect();
    let linked: Vec<Value> = c
        .linked
        .iter()
        .map(|lc| {
            let lr = evmdec::analyze::analyze(lc);
            let lmd = evmdec::analyze::render_markdown(
                lc,
                &lr,
                &format!("linked contract {}", lc.address.as_deref().unwrap_or("?")),
            );
            let ldis: Vec<String> = evmdec::disasm::disassemble(&lc.info.runtime)
                .iter()
                .map(evmdec::disasm::format_instruction)
                .collect();
            json!({"contract": lc, "report": lr, "report_markdown": lmd, "disassembly": ldis})
        })
        .collect();
    let mut v = json!({"contract": c, "report": r, "report_markdown": md, "disassembly": disasm});
    if !linked.is_empty() {
        v["linked"] = Value::Array(linked);
    }
    Ok(v)
}

async fn api_decompile(
    State(st): State<AppState>,
    Json(req): Json<DecompileReq>,
) -> axum::response::Response {
    let chain = req.chain.clone().unwrap_or_else(|| "mainnet".into());
    let key = format!(
        "{}|{}|{}|{}|{}",
        req.bytecode.as_deref().unwrap_or(""),
        req.address.as_deref().unwrap_or("").to_lowercase(),
        chain,
        req.no_follow_proxy,
        req.lookup
    );
    if let Some(v) = st
        .cache
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&key)
        .cloned()
    {
        return Json((*v).clone()).into_response();
    }
    let result = tokio::task::spawn_blocking(move || -> Result<Value, (StatusCode, String)> {
        let lookup = if req.lookup {
            Lookup::Online
        } else {
            Lookup::Offline
        };
        if let Some(addr) = req.address.as_deref().filter(|a| !a.trim().is_empty()) {
            let addr = addr.trim().to_string();
            if !evmdec::rpc::is_address(&addr) {
                return Err((StatusCode::BAD_REQUEST, "invalid address".into()));
            }
            let source = Source::Address {
                address: &addr,
                chain: &chain,
                rpc: req.rpc.as_deref(),
                policy: Policy {
                    follow: !req.no_follow_proxy,
                    ..Policy::default()
                },
            };
            return run(&source, lookup).map_err(|e| {
                let status = if e.contains("has no code") {
                    StatusCode::NOT_FOUND
                } else {
                    StatusCode::BAD_GATEWAY
                };
                (status, e)
            });
        }
        let hex = req.bytecode.unwrap_or_default();
        let code = evmdec::hex::decode(&hex).map_err(|e| (StatusCode::BAD_REQUEST, e))?;
        if code.is_empty() {
            return Err((StatusCode::BAD_REQUEST, "empty bytecode".into()));
        }
        if code.len() > 1 << 20 {
            return Err((StatusCode::BAD_REQUEST, "bytecode too large".into()));
        }
        run(&Source::Bytecode(&code), lookup).map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e))
    })
    .await;
    match result {
        Ok(Ok(v)) => {
            let v = Arc::new(v);
            let mut cache = st
                .cache
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if cache.len() > 256 {
                cache.clear();
            }
            cache.insert(key, v.clone());
            Json((*v).clone()).into_response()
        }
        Ok(Err((status, msg))) => error(status, msg),
        Err(e) => error(
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("decompiler panicked: {}", e),
        ),
    }
}

async fn api_address(
    State(st): State<AppState>,
    Path((chain, address)): Path<(String, String)>,
) -> axum::response::Response {
    api_decompile(
        State(st),
        Json(DecompileReq {
            address: Some(address),
            chain: Some(chain),
            ..Default::default()
        }),
    )
    .await
}

/// The page, with `__ORIGIN__` (used by the Open Graph tags, which need absolute URLs) replaced
/// by the scheme and host this request arrived on.
async fn index(headers: header::HeaderMap) -> Html<String> {
    let host = headers
        .get(header::HOST)
        .and_then(|h| h.to_str().ok())
        .unwrap_or("localhost:8080");
    let proto = headers
        .get("x-forwarded-proto")
        .and_then(|h| h.to_str().ok())
        .unwrap_or(
            if host.starts_with("localhost") || host.starts_with("127.") {
                "http"
            } else {
                "https"
            },
        );
    Html(INDEX.replace("__ORIGIN__", &format!("{}://{}", proto, host)))
}

async fn og_image() -> impl IntoResponse {
    (
        [
            (header::CONTENT_TYPE, "image/png"),
            (header::CACHE_CONTROL, "public, max-age=86400"),
        ],
        OG_PNG,
    )
}

async fn favicon() -> impl IntoResponse {
    (
        [
            (header::CONTENT_TYPE, "image/svg+xml"),
            (header::CACHE_CONTROL, "public, max-age=86400"),
        ],
        FAVICON,
    )
}

async fn robots() -> &'static str {
    "User-agent: *\nAllow: /\nDisallow: /api/\n"
}

async fn healthz() -> &'static str {
    "ok"
}

async fn chains() -> Json<Value> {
    Json(json!(evmdec::rpc::CHAINS
        .iter()
        .map(|c| json!({"name": c.name, "id": c.id}))
        .collect::<Vec<_>>()))
}

#[tokio::main]
async fn main() {
    let port: u16 = std::env::var("PORT")
        .ok()
        .and_then(|p| p.parse().ok())
        .unwrap_or(8080);
    let app = Router::new()
        .route("/", get(index))
        .route("/healthz", get(healthz))
        .route("/og.png", get(og_image))
        .route("/favicon.svg", get(favicon))
        .route("/favicon.ico", get(favicon))
        .route("/robots.txt", get(robots))
        .route("/api/chains", get(chains))
        .route("/api/decompile", post(api_decompile))
        .route("/api/address/{chain}/{address}", get(api_address))
        .layer(tower_http::cors::CorsLayer::permissive())
        .with_state(AppState::default());
    let addr = format!("0.0.0.0:{}", port);
    eprintln!("evmdec-server listening on http://{}", addr);
    let listener = tokio::net::TcpListener::bind(&addr).await.expect("bind");
    axum::serve(listener, app).await.expect("serve");
}
