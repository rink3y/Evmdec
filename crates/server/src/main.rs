use axum::body::Bytes;
use axum::extract::rejection::JsonRejection;
use axum::extract::{DefaultBodyLimit, Path, State};
use axum::http::{header, HeaderMap, HeaderValue, StatusCode};
use axum::response::{Html, IntoResponse};
use axum::routing::{get, post};
use axum::{Json, Router};
use evmdec::decompile::{Contract, Options};
use evmdec::fetch::{CodeCache, Policy};
use evmdec::rpc::Client;
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tokio::sync::Semaphore;

const INDEX: &str = include_str!("../static/index.html");
const OG_PNG: &[u8] = include_bytes!("../static/og.png");
const FAVICON: &str = include_str!("../static/favicon.svg");

struct Cached {
    body: Bytes,
    made: Instant,
    expires: bool,
}

/* Every caller of the public API draws on one pool, which is full again at midnight UTC.
shortcut: the count lives in this process, so a restart refills it and two servers each
keep their own. Move it to a file or a shared store when either matters. */
struct Pool {
    limit: u32,
    day: u64,
    used: u32,
}

const DAY: u64 = 86_400;
const API_DAILY: u32 = 5000;

impl Pool {
    fn take(&mut self, now: u64) -> Result<u32, u64> {
        if now / DAY != self.day {
            (self.day, self.used) = (now / DAY, 0);
        }
        if self.used >= self.limit {
            return Err(DAY - now % DAY);
        }
        self.used += 1;
        Ok(self.limit - self.used)
    }
}

#[derive(Clone)]
struct AppState {
    cache: Arc<Mutex<HashMap<[u8; 32], Cached>>>,
    slots: Arc<Semaphore>,
    waiting: Arc<AtomicUsize>,
    pool: Arc<Mutex<Pool>>,
}

impl Default for AppState {
    fn default() -> Self {
        let limit = std::env::var("EVMDEC_API_DAILY").ok();
        let limit = limit.and_then(|l| l.parse().ok()).unwrap_or(API_DAILY);
        let pool = Pool {
            limit,
            day: 0,
            used: 0,
        };
        AppState {
            cache: Arc::default(),
            slots: Arc::new(Semaphore::new(MAX_IN_FLIGHT)),
            waiting: Arc::default(),
            pool: Arc::new(Mutex::new(pool)),
        }
    }
}

const MAX_IN_FLIGHT: usize = 4;
const MAX_WAITING: usize = 16;
const MAX_CODE: usize = 1 << 20;
// Hex doubles the code and the JSON around it adds a little.
const MAX_BODY: usize = 2 * MAX_CODE + 4096;
const MAX_CACHED: usize = 64;
const MAX_CACHED_BYTES: usize = 96 << 20;
// An address can point at new code after an upgrade. Pasted code never changes.
const ADDRESS_KEPT: Duration = Duration::from_secs(600);
// The work stops itself before the client is told it took too long,
// so a slot is never held by work nobody is waiting for.
const WORK_TIME: Duration = Duration::from_secs(240);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(300);

#[derive(Deserialize, Default)]
struct DecompileReq {
    bytecode: Option<String>,
    address: Option<String>,
    chain: Option<String>,
    #[serde(default)]
    no_follow_proxy: bool,
    depth: Option<usize>,
    #[serde(default)]
    lookup: bool,
}

struct Waiting(Arc<AtomicUsize>);

impl Drop for Waiting {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::SeqCst);
    }
}

fn cached(st: &AppState, key: &[u8; 32]) -> Option<Bytes> {
    let mut cache = st
        .cache
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let entry = cache.get(key)?;
    if entry.expires && entry.made.elapsed() > ADDRESS_KEPT {
        cache.remove(key);
        return None;
    }
    Some(entry.body.clone())
}

fn keep(st: &AppState, key: [u8; 32], body: Bytes, expires: bool) {
    let mut cache = st
        .cache
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let held: usize = cache.values().map(|c| c.body.len()).sum();
    if cache.len() >= MAX_CACHED || held + body.len() > MAX_CACHED_BYTES {
        cache.clear();
    }
    cache.insert(
        key,
        Cached {
            body,
            made: Instant::now(),
            expires,
        },
    );
}

fn json_body(body: Bytes) -> axum::response::Response {
    ([(header::CONTENT_TYPE, "application/json")], body).into_response()
}

fn error(status: StatusCode, msg: impl Into<String>) -> axum::response::Response {
    (status, Json(json!({"error": msg.into()}))).into_response()
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
        policy: Policy,
    },
}

impl Source<'_> {
    fn obtain(&self, opts: &Options, cache: &mut CodeCache) -> Result<Contract, String> {
        match self {
            Source::Bytecode(code) => Ok(evmdec::decompile::decompile(code, opts)),
            Source::Address {
                address,
                chain,
                policy,
            } => {
                let client = Client::new(None, chain)?;
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
        let sels = c.unknown_selectors();
        if !sels.is_empty() {
            opts.extra_sigs = evmdec::sigs::lookup_online(&sels);
            if !opts.extra_sigs.is_empty() {
                c = source.obtain(&opts, &mut cache)?;
            }
        }
    }
    let disasm: Vec<String> = evmdec::disasm::disassemble(&c.info.runtime)
        .iter()
        .map(evmdec::disasm::format_instruction)
        .collect();
    let linked: Vec<Value> = c
        .linked
        .iter()
        .map(|lc| {
            let ldis: Vec<String> = evmdec::disasm::disassemble(&lc.info.runtime)
                .iter()
                .map(evmdec::disasm::format_instruction)
                .collect();
            json!({"contract": lc, "disassembly": ldis})
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
    let mut v = json!({"contract": c, "disassembly": disasm});
    if !linked.is_empty() {
        v["linked"] = Value::Array(linked);
    }
    if !parts_disassembly.is_empty() {
        v["parts_disassembly"] = json!(parts_disassembly);
    }
    Ok(v)
}

enum Input {
    Address(String),
    Code(Vec<u8>),
}

fn input_of(req: &DecompileReq) -> Result<Input, String> {
    if let Some(address) = req.address.as_deref().map(str::trim) {
        if !address.is_empty() {
            return match evmdec::rpc::is_address(address) {
                true => Ok(Input::Address(address.to_ascii_lowercase())),
                false => Err("invalid address".into()),
            };
        }
    }
    let code = evmdec::hex::decode(req.bytecode.as_deref().unwrap_or_default())?;
    match code.len() {
        0 => Err("empty bytecode".into()),
        n if n > MAX_CODE => Err("bytecode too large".into()),
        _ => Ok(Input::Code(code)),
    }
}

struct Asked {
    input: Input,
    chain: String,
    follow: bool,
    lookup: Lookup,
    depth: usize,
}

type Refused = (StatusCode, String);

fn asked(request: Result<Json<DecompileReq>, JsonRejection>) -> Result<Asked, Refused> {
    let Json(req) = request.map_err(|r| (r.status(), r.body_text()))?;
    let chain = req.chain.clone().unwrap_or_else(|| "mainnet".into());
    let input = input_of(&req).map_err(|msg| (StatusCode::BAD_REQUEST, msg))?;
    if evmdec::rpc::chain_by_name(&chain).is_none() {
        return Err((StatusCode::BAD_REQUEST, format!("unknown chain '{chain}'")));
    }
    Ok(Asked {
        input,
        chain,
        follow: !req.no_follow_proxy,
        lookup: match req.lookup {
            true => Lookup::Online,
            false => Lookup::Offline,
        },
        depth: req.depth.unwrap_or(Policy::default().depth).min(3),
    })
}

async fn answer(st: &AppState, asked: Asked) -> axum::response::Response {
    let Asked {
        input,
        chain,
        follow,
        lookup,
        depth,
    } = asked;
    let mut label = format!(
        "{}|{}|{}|{}|",
        chain,
        !follow,
        lookup == Lookup::Online,
        depth
    )
    .into_bytes();
    match &input {
        Input::Address(address) => label.extend_from_slice(address.as_bytes()),
        Input::Code(code) => label.extend_from_slice(&evmdec::keccak::keccak256(code)),
    }
    let key = evmdec::keccak::keccak256(&label);
    if let Some(body) = cached(st, &key) {
        return json_body(body);
    }
    if st.waiting.fetch_add(1, Ordering::SeqCst) >= MAX_WAITING {
        st.waiting.fetch_sub(1, Ordering::SeqCst);
        return error(
            StatusCode::SERVICE_UNAVAILABLE,
            "the server is busy, try again in a minute",
        );
    }
    let waiting = Waiting(st.waiting.clone());
    let Ok(slot) = st.slots.clone().acquire_owned().await else {
        return error(StatusCode::SERVICE_UNAVAILABLE, "server is shutting down");
    };
    drop(waiting);
    // Someone else may have finished the same input while this request waited.
    if let Some(body) = cached(st, &key) {
        return json_body(body);
    }
    let expires = matches!(input, Input::Address(_));
    let work = tokio::task::spawn_blocking(move || {
        // The slot is given back when the work ends, not when the client stops waiting.
        let _slot = slot;
        evmdec::clock::on_worker(|| {
            evmdec::clock::run(WORK_TIME, || {
                let source = match &input {
                    Input::Code(code) => Source::Bytecode(code),
                    Input::Address(address) => Source::Address {
                        address,
                        chain: &chain,
                        policy: Policy {
                            follow,
                            depth,
                            ..Policy::default()
                        },
                    },
                };
                run(&source, lookup).map(|v| Bytes::from(v.to_string()))
            })
        })
    });
    let outcome = match tokio::time::timeout(REQUEST_TIMEOUT, work).await {
        Ok(Ok(Ok(outcome))) => outcome,
        Ok(_) => {
            return error(
                StatusCode::INTERNAL_SERVER_ERROR,
                "the decompiler failed on this input",
            )
        }
        Err(_) => None,
    };
    match outcome {
        Some(Ok(body)) => {
            keep(st, key, body.clone(), expires);
            json_body(body)
        }
        Some(Err(msg)) => {
            let status = match (expires, msg.contains("has no code")) {
                (true, true) => StatusCode::NOT_FOUND,
                (true, false) => StatusCode::BAD_GATEWAY,
                (false, _) => StatusCode::INTERNAL_SERVER_ERROR,
            };
            error(status, msg)
        }
        None => error(
            StatusCode::GATEWAY_TIMEOUT,
            "decompiling took longer than the server allows",
        ),
    }
}

/* The page's own address is kept for the page, so that a script draws on the shared pool.
shortcut: a script can send the headers a browser sends. This keeps an honest caller on
the public API and stops nobody determined. Sign the page's requests if that matters. */
fn from_the_page(headers: &HeaderMap) -> bool {
    match headers.get("sec-fetch-site") {
        Some(site) => site == "same-origin",
        // A browser too old to say where a request comes from still names an origin.
        None => headers.contains_key(header::ORIGIN),
    }
}

async fn page_decompile(
    State(st): State<AppState>,
    headers: HeaderMap,
    request: Result<Json<DecompileReq>, JsonRejection>,
) -> axum::response::Response {
    if !from_the_page(&headers) {
        return error(
            StatusCode::FORBIDDEN,
            "this address serves the website, the public API is POST /v1/decompile",
        );
    }
    match asked(request) {
        Ok(asked) => answer(&st, asked).await,
        Err((status, said)) => error(status, said),
    }
}

async fn metered(st: &AppState, asked: Result<Asked, Refused>) -> axum::response::Response {
    let asked = match asked {
        Ok(asked) => asked,
        Err((status, said)) => return error(status, said),
    };
    let since = SystemTime::now().duration_since(UNIX_EPOCH);
    let now = since.map_or(0, |d| d.as_secs());
    let (limit, taken) = {
        let mut pool = st.pool.lock().unwrap_or_else(|e| e.into_inner());
        (pool.limit, pool.take(now))
    };
    let (mut answer, left) = match taken {
        Ok(left) => (answer(st, asked).await, left),
        Err(wait) => {
            let said = format!(
                "the shared pool of {limit} requests a day is used up, it is full again at 00:00 UTC"
            );
            let mut refused = error(StatusCode::TOO_MANY_REQUESTS, said);
            let headers = refused.headers_mut();
            headers.insert(header::RETRY_AFTER, HeaderValue::from(wait));
            (refused, 0)
        }
    };
    let facts = [
        ("x-ratelimit-limit", u64::from(limit)),
        ("x-ratelimit-remaining", u64::from(left)),
        ("x-ratelimit-reset", now - now % DAY + DAY),
    ];
    for (name, value) in facts {
        answer.headers_mut().insert(name, HeaderValue::from(value));
    }
    answer
}

async fn api_decompile(
    State(st): State<AppState>,
    request: Result<Json<DecompileReq>, JsonRejection>,
) -> axum::response::Response {
    metered(&st, asked(request)).await
}

async fn api_address(
    State(st): State<AppState>,
    Path((chain, address)): Path<(String, String)>,
) -> axum::response::Response {
    let req = DecompileReq {
        address: Some(address),
        chain: Some(chain),
        ..Default::default()
    };
    metered(&st, asked(Ok(Json(req)))).await
}

// These two values are written into the page, so only plain ones are taken from a request.
fn plain_host(host: &str) -> bool {
    let allowed = |c: char| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | ':' | '[' | ']');
    !host.is_empty() && host.len() <= 255 && host.chars().all(allowed)
}

async fn index(headers: header::HeaderMap) -> Html<String> {
    let host = headers
        .get(header::HOST)
        .and_then(|h| h.to_str().ok())
        .filter(|h| plain_host(h))
        .unwrap_or("localhost:8080");
    let local = host.starts_with("localhost") || host.starts_with("127.");
    let proto = headers
        .get("x-forwarded-proto")
        .and_then(|h| h.to_str().ok())
        .filter(|p| matches!(*p, "http" | "https"))
        .unwrap_or(if local { "http" } else { "https" });
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
        .route("/api/decompile", post(page_decompile))
        .route("/v1/decompile", post(api_decompile))
        .route("/v1/address/{chain}/{address}", get(api_address))
        .route("/api/address/{chain}/{address}", get(api_address))
        .layer(DefaultBodyLimit::max(MAX_BODY))
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

#[cfg(test)]
mod tests {
    use super::{Pool, DAY};

    #[test]
    fn the_pool_runs_out_and_is_full_again_the_next_day() {
        let mut pool = Pool {
            limit: 2,
            day: 0,
            used: 0,
        };
        let noon = 20_000 * DAY + DAY / 2;
        assert_eq!(pool.take(noon), Ok(1));
        assert_eq!(pool.take(noon + 1), Ok(0));
        assert_eq!(pool.take(noon + 2), Err(DAY / 2 - 2));
        assert_eq!(pool.take(noon + DAY / 2), Ok(1));
    }
}
