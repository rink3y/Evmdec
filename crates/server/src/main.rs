//! evmdec web service: decompile by address or bytecode, serve the single-page UI.

use axum::{
    extract::{Path, State},
    http::{header, StatusCode},
    response::{Html, IntoResponse},
    routing::{get, post},
    Json, Router,
};
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

const INDEX: &str = include_str!("../static/index.html");

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
}

fn error(status: StatusCode, msg: impl Into<String>) -> axum::response::Response {
    (status, Json(json!({"error": msg.into()}))).into_response()
}

/// Run the decompiler and analyzer; returns the JSON document the UI consumes.
fn run(code: &[u8], address: Option<&str>, chain: Option<&str>, rpc: Option<&str>, follow: bool) -> Result<Value, String> {
    let opts = evmdec::decompile::Options::default();
    let mut c = evmdec::decompile::decompile(code, &opts);
    c.address = address.map(|s| s.to_string());
    c.chain = chain.map(|s| s.to_string());
    let mut implementation: Option<Value> = None;
    if let (Some(addr), Some(ch), true) = (address, chain, follow) {
        if let Ok(client) = evmdec::rpc::Client::new(rpc, ch) {
            let slots: Vec<evmdec::U256> = c.delegatecall_slots.iter().filter_map(|s| evmdec::U256::from_hex_str(s)).collect();
            let targets: Vec<evmdec::U256> = c.delegatecall_targets.iter().filter_map(|s| evmdec::U256::from_hex_str(s)).collect();
            if !slots.is_empty() || !targets.is_empty() || code.len() < 100 {
                if let Ok(Some(p)) = evmdec::rpc::resolve_proxy(&client, addr, code, &slots, &targets) {
                    if let Ok(ic) = client.get_code(&p.implementation) {
                        if !ic.is_empty() {
                            let mut icon = evmdec::decompile::decompile(&ic, &opts);
                            icon.address = Some(p.implementation.clone());
                            icon.chain = Some(ch.to_string());
                            icon.source = evmdec::decompile::render(&icon, "Implementation");
                            let ir = evmdec::analyze::analyze(&icon);
                            let imd = evmdec::analyze::render_markdown(&icon, &ir, &format!("implementation {}", p.implementation));
                            implementation = Some(json!({"contract": icon, "report": ir, "report_markdown": imd, "proxy_kind": p.kind, "admin": p.admin}));
                        }
                    }
                    c.proxy = Some(evmdec::decompile::ProxyRef { kind: p.kind, implementation: p.implementation, admin: p.admin, contract: None });
                }
            }
        }
    }
    let r = evmdec::analyze::analyze(&c);
    let md = evmdec::analyze::render_markdown(&c, &r, address.unwrap_or("bytecode"));
    let disasm: Vec<String> = evmdec::disasm::disassemble(&c.info.runtime).iter().map(evmdec::disasm::format_instruction).collect();
    let mut v = json!({"contract": c, "report": r, "report_markdown": md, "disassembly": disasm});
    if let Some(i) = implementation {
        v["implementation"] = i;
    }
    Ok(v)
}

async fn api_decompile(State(st): State<AppState>, Json(req): Json<DecompileReq>) -> axum::response::Response {
    let chain = req.chain.clone().unwrap_or_else(|| "mainnet".into());
    let key = format!("{}|{}|{}|{}", req.bytecode.as_deref().unwrap_or(""), req.address.as_deref().unwrap_or("").to_lowercase(), chain, req.no_follow_proxy);
    if let Some(v) = st.cache.lock().unwrap().get(&key).cloned() {
        return Json((*v).clone()).into_response();
    }
    let result = tokio::task::spawn_blocking(move || -> Result<Value, (StatusCode, String)> {
        if let Some(addr) = req.address.as_deref().filter(|a| !a.trim().is_empty()) {
            let addr = addr.trim().to_string();
            if !evmdec::rpc::is_address(&addr) {
                return Err((StatusCode::BAD_REQUEST, "invalid address".into()));
            }
            let client = evmdec::rpc::Client::new(req.rpc.as_deref(), &chain).map_err(|e| (StatusCode::BAD_REQUEST, e))?;
            let code = client.get_code(&addr).map_err(|e| (StatusCode::BAD_GATEWAY, e))?;
            if code.is_empty() {
                return Err((StatusCode::NOT_FOUND, format!("{} has no code on {}", addr, chain)));
            }
            return run(&code, Some(&addr), Some(&chain), req.rpc.as_deref(), !req.no_follow_proxy).map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e));
        }
        let hex = req.bytecode.unwrap_or_default();
        let code = evmdec::hex::decode(&hex).map_err(|e| (StatusCode::BAD_REQUEST, e))?;
        if code.is_empty() {
            return Err((StatusCode::BAD_REQUEST, "empty bytecode".into()));
        }
        if code.len() > 1 << 20 {
            return Err((StatusCode::BAD_REQUEST, "bytecode too large".into()));
        }
        run(&code, None, None, None, false).map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e))
    })
    .await;
    match result {
        Ok(Ok(v)) => {
            let v = Arc::new(v);
            let mut cache = st.cache.lock().unwrap();
            if cache.len() > 256 {
                cache.clear();
            }
            cache.insert(key, v.clone());
            Json((*v).clone()).into_response()
        }
        Ok(Err((status, msg))) => error(status, msg),
        Err(e) => error(StatusCode::INTERNAL_SERVER_ERROR, format!("decompiler panicked: {}", e)),
    }
}

async fn api_address(State(st): State<AppState>, Path((chain, address)): Path<(String, String)>) -> axum::response::Response {
    api_decompile(State(st), Json(DecompileReq { address: Some(address), chain: Some(chain), ..Default::default() })).await
}

async fn index() -> Html<&'static str> {
    Html(INDEX)
}

async fn healthz() -> &'static str {
    "ok"
}

async fn chains() -> Json<Value> {
    Json(json!(evmdec::rpc::CHAINS.iter().map(|c| json!({"name": c.name, "id": c.id})).collect::<Vec<_>>()))
}

#[tokio::main]
async fn main() {
    let port: u16 = std::env::var("PORT").ok().and_then(|p| p.parse().ok()).unwrap_or(8080);
    let app = Router::new()
        .route("/", get(index))
        .route("/healthz", get(healthz))
        .route("/api/chains", get(chains))
        .route("/api/decompile", post(api_decompile))
        .route("/api/address/{chain}/{address}", get(api_address))
        .layer(tower_http::cors::CorsLayer::permissive())
        .with_state(AppState::default());
    let addr = format!("0.0.0.0:{}", port);
    eprintln!("evmdec-server listening on http://{}", addr);
    let listener = tokio::net::TcpListener::bind(&addr).await.expect("bind");
    let _ = header::CONTENT_TYPE;
    axum::serve(listener, app).await.expect("serve");
}
