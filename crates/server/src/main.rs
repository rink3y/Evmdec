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
use std::time::Duration;
use tokio::sync::Semaphore;

const INDEX: &str = include_str!("../static/index.html");
const OG_PNG: &[u8] = include_bytes!("../static/og.png");
const FAVICON: &str = include_str!("../static/favicon.svg");

#[derive(Clone)]
struct AppState {
    cache: Arc<Mutex<HashMap<String, Arc<Value>>>>,
    slots: Arc<Semaphore>,
}

impl Default for AppState {
    fn default() -> Self {
        AppState {
            cache: Arc::default(),
            slots: Arc::new(Semaphore::new(MAX_IN_FLIGHT)),
        }
    }
}

const MAX_IN_FLIGHT: usize = 4;
const REQUEST_TIMEOUT: Duration = Duration::from_secs(300);

#[derive(Deserialize, Default)]
struct DecompileReq {
    bytecode: Option<String>,
    address: Option<String>,
    chain: Option<String>,
    rpc: Option<String>,
    #[serde(default)]
    no_follow_proxy: bool,
    depth: Option<usize>,
    #[serde(default)]
    lookup: bool,
}

fn error(status: StatusCode, msg: impl Into<String>) -> axum::response::Response {
    (status, Json(json!({"error": msg.into()}))).into_response()
}

fn unknown_selectors(c: &Contract) -> Vec<u32> {
    c.functions
        .iter()
        .filter(|f| f.signature.is_none())
        .filter_map(|f| f.selector.as_ref())
        .filter_map(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lookup {
    Offline,
    Online,
}

enum Source<'a> {
    Bytecode(&'a [u8]),
    Address {
        address: &'a str,
        chain: &'a str,
        rpc: Option<&'a str>,
        policy: Policy,
    },
}

impl Source<'_> {
    fn title(&self) -> &str {
        match self {
            Source::Bytecode(_) => "bytecode",
            Source::Address { address, .. } => address,
        }
    }

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
    let parts_disassembly: Vec<Vec<String>> = c
        .parts
        .iter()
        .map(|p| {
            evmdec::disasm::disassemble(&p.runtime)
                .iter()
                .map(evmdec::disasm::format_instruction)
                .collect()
        })
        .collect();
    let mut v = json!({"contract": c, "report": r, "report_markdown": md, "disassembly": disasm});
    if !linked.is_empty() {
        v["linked"] = Value::Array(linked);
    }
    if !parts_disassembly.is_empty() {
        v["parts_disassembly"] = json!(parts_disassembly);
    }
    Ok(v)
}

async fn api_decompile(
    State(st): State<AppState>,
    Json(req): Json<DecompileReq>,
) -> axum::response::Response {
    let chain = req.chain.clone().unwrap_or_else(|| "mainnet".into());
    let key = format!(
        "{}|{}|{}|{}|{}|{:?}",
        req.bytecode.as_deref().unwrap_or(""),
        req.address.as_deref().unwrap_or("").to_lowercase(),
        chain,
        req.no_follow_proxy,
        req.lookup,
        req.depth
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
    let Ok(_slot) = st.slots.clone().acquire_owned().await else {
        return (StatusCode::SERVICE_UNAVAILABLE, "server is shutting down").into_response();
    };
    let work = tokio::task::spawn_blocking(move || -> Result<Value, (StatusCode, String)> {
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
                    depth: req.depth.unwrap_or(Policy::default().depth).min(3),
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
    });
    let result = match tokio::time::timeout(REQUEST_TIMEOUT, work).await {
        Ok(r) => r,
        Err(_) => {
            return (
                StatusCode::GATEWAY_TIMEOUT,
                "the request took longer than the server allows",
            )
                .into_response()
        }
    };
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

async fn status() -> Json<Value> {
    let signatures = evmdec::sigdb::global().map_or(0, evmdec::sigdb::SigDb::len);
    Json(json!({"signature_index": signatures}))
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
        .route("/api/status", get(status))
        .route("/api/decompile", post(api_decompile))
        .route("/api/address/{chain}/{address}", get(api_address))
        .layer(tower_http::cors::CorsLayer::permissive())
        .with_state(AppState::default());
    let addr = format!("0.0.0.0:{}", port);
    match evmdec::sigdb::global() {
        Some(db) => eprintln!("signature index: {} signatures", db.len()),
        None => eprintln!(
            "signature index: none, only the built-in dictionary names functions \
             (build one with corpus/build_sigs.py or set EVMDEC_SIGS)"
        ),
    }
    eprintln!("evmdec-server listening on http://{}", addr);
    let listener = tokio::net::TcpListener::bind(&addr).await.expect("bind");
    axum::serve(listener, app).await.expect("serve");
}
