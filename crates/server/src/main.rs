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
use serde::{Deserialize, Serialize};
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
    chainid: Option<u64>,
    #[serde(default)]
    full: bool,
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
    full: bool,
    chain: String,
    follow: bool,
    lookup: Lookup,
    depth: usize,
}

type Refused = (StatusCode, String);

fn asked(request: Result<Json<DecompileReq>, JsonRejection>) -> Result<Asked, Refused> {
    let Json(req) = request.map_err(|r| (r.status(), r.body_text()))?;
    let named = req.chain.clone().unwrap_or_else(|| "mainnet".into());
    let chain = req.chainid.map_or(named, |id| id.to_string());
    let input = input_of(&req).map_err(|msg| (StatusCode::BAD_REQUEST, msg))?;
    if evmdec::rpc::chain_by_name(&chain).is_none() {
        let said = format!("unknown chain '{chain}', GET /v1/chains lists the ones there are");
        return Err((StatusCode::BAD_REQUEST, said));
    }
    Ok(Asked {
        input,
        full: req.full,
        chain,
        follow: !req.no_follow_proxy,
        lookup: match req.lookup {
            true => Lookup::Online,
            false => Lookup::Offline,
        },
        depth: req.depth.unwrap_or(Policy::default().depth).min(3),
    })
}

async fn answer(st: &AppState, asked: Asked) -> Result<Bytes, Refused> {
    let Asked {
        input,
        chain,
        follow,
        lookup,
        depth,
        ..
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
        return Ok(body);
    }
    if st.waiting.fetch_add(1, Ordering::SeqCst) >= MAX_WAITING {
        st.waiting.fetch_sub(1, Ordering::SeqCst);
        let busy = "the server is busy, try again in a minute";
        return Err((StatusCode::SERVICE_UNAVAILABLE, busy.into()));
    }
    let waiting = Waiting(st.waiting.clone());
    let Ok(slot) = st.slots.clone().acquire_owned().await else {
        let closing = "server is shutting down";
        return Err((StatusCode::SERVICE_UNAVAILABLE, closing.into()));
    };
    drop(waiting);
    // Someone else may have finished the same input while this request waited.
    if let Some(body) = cached(st, &key) {
        return Ok(body);
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
            let failed = "the decompiler failed on this input";
            return Err((StatusCode::INTERNAL_SERVER_ERROR, failed.into()));
        }
        Err(_) => None,
    };
    match outcome {
        Some(Ok(body)) => {
            keep(st, key, body.clone(), expires);
            Ok(body)
        }
        Some(Err(msg)) => {
            let status = match (expires, msg.contains("has no code")) {
                (true, true) => StatusCode::NOT_FOUND,
                (true, false) => StatusCode::BAD_GATEWAY,
                (false, _) => StatusCode::INTERNAL_SERVER_ERROR,
            };
            Err((status, msg))
        }
        None => {
            let slow = "decompiling took longer than the server allows";
            Err((StatusCode::GATEWAY_TIMEOUT, slow.into()))
        }
    }
}

#[derive(Serialize)]
struct Called {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    selector: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    signature: Option<String>,
    mutability: String,
}

#[derive(Serialize)]
struct Kept {
    name: String,
    slot: String,
    #[serde(rename = "type")]
    ty: String,
}

#[derive(Serialize)]
struct Shown {
    role: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    address: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reached_from: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reached_how: Option<String>,
    compiler: String,
    source: String,
    functions: Vec<Called>,
    storage: Vec<Kept>,
}

#[derive(Serialize)]
struct Missed {
    address: String,
    seen_in: String,
    reason: String,
}

#[derive(Serialize)]
struct Lean {
    #[serde(skip_serializing_if = "Option::is_none")]
    address: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    chainid: Option<u64>,
    summary: String,
    contracts: Vec<Shown>,
    not_fetched: Vec<Missed>,
    checked: bool,
}

fn text(of: &Value) -> String {
    of.as_str().unwrap_or_default().to_string()
}

fn known(of: &Value) -> Option<String> {
    of.as_str().map(str::to_string)
}

fn each(of: &Value) -> impl Iterator<Item = &Value> {
    of.as_array().into_iter().flatten()
}

fn called(c: &Value, part: Option<usize>) -> Vec<Called> {
    let of_part = |f: &&Value| part.is_none_or(|p| f["part"].as_u64().unwrap_or(0) == p as u64);
    let outside = each(&c["functions"]).filter(|f| f["kind"] == "external");
    let one = |f: &Value| Called {
        name: text(&f["name"]),
        selector: known(&f["selector"]),
        signature: known(&f["signature"]),
        mutability: text(&f["mutability"]).replace('_', ""),
    };
    outside.filter(of_part).map(one).collect()
}

fn kept(storage: &Value) -> Vec<Kept> {
    let one = |v: &Value| Kept {
        name: text(&v["name"]),
        slot: text(&v["slot"]),
        ty: text(&v["ty"]),
    };
    each(storage).map(one).collect()
}

fn count(n: usize, what: &str) -> String {
    match n {
        1 => format!("1 {what}"),
        n => format!("{n} {what}s"),
    }
}

/* The public answer: every contract in one list and one shape, with what a reader came
for first and nothing a reader has to know the decompiler to use. */
fn lean(full: &Value, chain: &str) -> Lean {
    let c = &full["contract"];
    let diamond = each(&c["parts"]).any(|p| p["role"] == "facet");
    let part = |(i, part): (usize, &Value)| Shown {
        role: match part["role"].as_str() {
            Some("shell") if diamond => "diamond".into(),
            Some("shell") => "proxy".into(),
            role => role.unwrap_or("contract").into(),
        },
        address: known(&part["address"]),
        reached_from: None,
        reached_how: None,
        compiler: text(&part["compiler"]),
        source: text(&part["source"]),
        functions: called(c, Some(i)),
        storage: kept(&part["storage"]),
    };
    let whole = |c: &Value, role: &str| Shown {
        role: role.into(),
        address: known(&c["address"]),
        reached_from: known(&c["link"]["from"]),
        reached_how: known(&c["link"]["how"]),
        compiler: text(&c["language"]),
        source: text(&c["source"]),
        functions: called(c, None),
        storage: kept(&c["storage"]),
    };
    let mut contracts: Vec<Shown> = each(&c["parts"]).enumerate().map(part).collect();
    // A reader of a proxy came for the code behind it.
    if contracts.len() == 2 && contracts[1].role == "implementation" {
        contracts.swap(0, 1);
    }
    if contracts.is_empty() {
        contracts.push(whole(c, "contract"));
    }
    let parts = contracts.len();
    let library = |lc: &Value| text(&lc["link"]["how"]).starts_with("library");
    let linked = each(&full["linked"]).map(|entry| &entry["contract"]);
    contracts.extend(linked.map(|lc| whole(lc, if library(lc) { "library" } else { "linked" })));
    let mut summary = match (c["proxy"]["kind"].as_str(), parts) {
        (Some(kind), _) => {
            let behind = c["proxy"]["implementation"].as_str();
            format!(
                "{kind}. Implementation at {}.",
                behind.unwrap_or("an unknown address")
            )
        }
        (None, 1) => {
            let outside = count(contracts[0].functions.len(), "external function");
            format!(
                "One contract with {outside}, built with {}.",
                contracts[0].compiler
            )
        }
        (None, n) => format!("A contract made of {n} parts."),
    };
    if contracts.len() > parts {
        let followed = count(contracts.len() - parts, "linked contract");
        summary.push_str(&format!(" {followed} followed."));
    }
    let missed = |m: &Value| Missed {
        address: text(&m["target"]),
        seen_in: text(&m["from"]),
        reason: text(&m["reason"]),
    };
    let not_fetched: Vec<Missed> = each(&c["unfollowed"]).map(missed).collect();
    if !not_fetched.is_empty() {
        let seen = count(not_fetched.len(), "contract");
        summary.push_str(&format!(" {seen} seen and not fetched."));
    }
    let address = known(&c["address"]);
    Lean {
        chainid: address
            .as_ref()
            .and(evmdec::rpc::chain_by_name(chain))
            .map(|c| c.id),
        address,
        summary,
        contracts,
        not_fetched,
        // The text is written as first made. No compiler has taken it and nothing ran it.
        checked: false,
    }
}

fn leaned(full: &[u8], chain: &str) -> axum::response::Response {
    match serde_json::from_slice::<Value>(full) {
        Ok(full) => Json(lean(&full, chain)).into_response(),
        Err(_) => error(
            StatusCode::INTERNAL_SERVER_ERROR,
            "the answer could not be read",
        ),
    }
}

// Written out as text so that a reader gets the fields in this order.
const DESCRIBED: &str = r#"{
  "name": "evmdec",
  "what": "Decompiles EVM bytecode, or the contract at an address, into a Solidity file.",
  "endpoints": {
    "POST /v1/decompile": "Decompile bytecode or an address. JSON body, fields under request.",
    "GET /v1/address/{chainid}/{address}": "The same for an address, with every default.",
    "GET /v1/chains": "The chains an address can be on, each with its name and id.",
    "GET /v1": "This description."
  },
  "request": {
    "bytecode": "Hex of the code, with or without 0x, at most 1 MiB. Give this or address.",
    "address": "A contract address, 0x and 40 hex digits. Give this or bytecode.",
    "chainid": "Number of the chain the address is on, such as 1 or 56. Default 1.",
    "depth": "How many calls away from the address other contracts are followed, 0 to 3. Default 2.",
    "no_follow_proxy": "true to leave a proxy without its implementation. Default false.",
    "lookup": "true to look up unknown selectors online. Default false.",
    "full": "true for every detail the decompiler has, with the disassembly. Default false."
  },
  "answer": {
    "address": "The address asked for. Absent for bytecode.",
    "chainid": "The chain it is on. Absent for bytecode.",
    "summary": "One sentence saying what came back.",
    "contracts": "Every contract in one list, the one a reader came for first.",
    "contracts[].role": "contract, proxy, implementation, diamond, facet, library or linked.",
    "contracts[].address": "Where that contract is. Absent for bytecode.",
    "contracts[].reached_from": "For a library or linked contract: the contract that leads to it.",
    "contracts[].reached_how": "For a library or linked contract: how the other one uses it.",
    "contracts[].compiler": "The compiler that built it.",
    "contracts[].source": "The Solidity file of that contract.",
    "contracts[].functions": "The functions callable from outside: name, selector, signature, mutability.",
    "contracts[].storage": "The state variables: name, slot, type.",
    "not_fetched": "Contracts that were seen and not fetched: address, seen_in, reason.",
    "checked": "Always false. The source is not compiled or run before it is sent."
  },
  "limits": {
    "requests_a_day": __LIMIT__,
    "shared_by": "every caller together",
    "refills_at": "00:00 UTC",
    "headers": "x-ratelimit-limit, x-ratelimit-remaining and x-ratelimit-reset on every answer",
    "when_empty": "status 429 with retry-after in seconds"
  },
  "errors": "Every refusal is JSON of the form {\"error\": \"...\"}, with status 400, 404, 429, 502, 503 or 504.",
  "example": "POST /v1/decompile {\"address\": \"0xdAC17F958D2ee523a2206206994597C13D831ec7\", \"chainid\": 1}"
}
"#;

async fn described(State(st): State<AppState>) -> axum::response::Response {
    let limit = st.pool.lock().unwrap_or_else(|e| e.into_inner()).limit;
    json_body(Bytes::from(
        DESCRIBED.replace("__LIMIT__", &limit.to_string()),
    ))
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
    let answered = match asked(request) {
        Ok(asked) => answer(&st, asked).await,
        Err(refused) => Err(refused),
    };
    match answered {
        Ok(body) => json_body(body),
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
    let (full, chain) = (asked.full, asked.chain.clone());
    let (mut answer, left) = match taken {
        Ok(left) => match answer(st, asked).await {
            Ok(body) if full => (json_body(body), left),
            Ok(body) => (leaned(&body, &chain), left),
            Err((status, said)) => (error(status, said), left),
        },
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
        .route("/v1", get(described))
        .route("/v1/chains", get(chains))
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
    use super::{lean, Pool, DAY};
    use serde_json::json;

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

    #[test]
    fn the_public_answer_lists_every_contract_once_with_the_one_asked_for_first() {
        let function = |name: &str, part: u64| {
            json!({"kind": "external", "name": name, "selector": "0x01020304",
                   "mutability": "non_payable", "part": part})
        };
        let full = json!({
            "contract": {
                "address": "0xaa",
                "proxy": {"kind": "EIP-1967 proxy", "implementation": "0xbb"},
                "functions": [function("upgradeTo", 0), function("transfer", 1),
                              {"kind": "internal", "name": "_move", "part": 1}],
                "parts": [
                    {"role": "shell", "address": "0xaa", "compiler": "solc 0.8.20",
                     "source": "proxy text", "storage": []},
                    {"role": "implementation", "address": "0xbb", "compiler": "solc 0.8.28",
                     "source": "token text",
                     "storage": [{"name": "owner", "slot": "0x0", "ty": "address"}]},
                ],
                "unfollowed": [{"target": "0xdd", "from": "0xbb", "reason": "the depth"}],
            },
            "linked": [{"contract": {
                "address": "0xcc", "language": "solc 0.8.28", "source": "library text",
                "link": {"from": "0xbb", "how": "library, run in the caller's storage", "depth": 1},
                "functions": [], "storage": [],
            }}],
        });
        let answer = serde_json::to_value(lean(&full, "56")).expect("the answer is JSON");
        let roles: Vec<&str> = answer["contracts"]
            .as_array()
            .expect("a list")
            .iter()
            .map(|c| c["role"].as_str().expect("a role"))
            .collect();
        assert_eq!(roles, ["implementation", "proxy", "library"]);
        assert_eq!(answer["chainid"], 56);
        assert_eq!(answer["checked"], false);
        let token = &answer["contracts"][0];
        assert_eq!(token["source"], "token text");
        assert_eq!(
            token["functions"],
            json!([{"name": "transfer", "selector": "0x01020304",
                                               "mutability": "nonpayable"}])
        );
        assert_eq!(
            token["storage"],
            json!([{"name": "owner", "slot": "0x0", "type": "address"}])
        );
        assert_eq!(answer["contracts"][2]["reached_from"], "0xbb");
        assert_eq!(answer["not_fetched"][0]["address"], "0xdd");
        assert_eq!(
            answer["summary"],
            "EIP-1967 proxy. Implementation at 0xbb. 1 linked contract followed. \
             1 contract seen and not fetched."
        );
    }
}
