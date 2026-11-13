use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

struct Server {
    child: Child,
    port: u16,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn start() -> Server {
    let free = TcpListener::bind("127.0.0.1:0").expect("a port is free");
    let port = free.local_addr().expect("the port is known").port();
    drop(free);
    let child = Command::new(env!("CARGO_BIN_EXE_evmdec-server"))
        .env("PORT", port.to_string())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("the server starts");
    let server = Server { child, port };
    let until = Instant::now() + Duration::from_secs(20);
    while TcpStream::connect(("127.0.0.1", port)).is_err() {
        assert!(Instant::now() < until, "the server did not start listening");
        std::thread::sleep(Duration::from_millis(50));
    }
    server
}

fn send(server: &Server, request: &str) -> String {
    let mut stream = TcpStream::connect(("127.0.0.1", server.port)).expect("the server accepts");
    stream
        .set_read_timeout(Some(Duration::from_secs(120)))
        .expect("a timeout can be set");
    stream
        .write_all(request.as_bytes())
        .expect("the request is sent");
    let mut answer = Vec::new();
    let _ = stream.read_to_end(&mut answer);
    String::from_utf8_lossy(&answer).into_owned()
}

fn post(server: &Server, body: &str) -> String {
    send(
        server,
        &format!(
            "POST /api/decompile HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/json\r\n\
             Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
            body.len()
        ),
    )
}

fn body(answer: &str) -> &str {
    answer.split_once("\r\n\r\n").map_or("", |(_, body)| body)
}

const STORE_ONE: &str = "0x600160005500";
const STORE_TWO: &str = "0x6002600055600360015500";

#[test]
fn each_input_gets_its_own_answer_and_a_repeat_gets_the_same_one() {
    let server = start();
    let ask = |code: &str| post(&server, &format!("{{\"bytecode\":\"{code}\"}}"));
    let (one, two, again) = (ask(STORE_ONE), ask(STORE_TWO), ask(STORE_ONE));
    assert!(one.starts_with("HTTP/1.1 200"), "{one}");
    assert!(body(&one).contains("\"contract\""));
    assert_ne!(body(&one), body(&two));
    assert_eq!(body(&one), body(&again));
}

#[test]
fn a_node_named_in_the_request_changes_nothing() {
    let server = start();
    let plain = post(&server, &format!("{{\"bytecode\":\"{STORE_ONE}\"}}"));
    let named = format!("{{\"bytecode\":\"{STORE_ONE}\",\"rpc\":\"http://127.0.0.1:9/\"}}");
    assert_eq!(body(&plain), body(&post(&server, &named)));
}

#[test]
fn every_refusal_is_json() {
    let server = start();
    for request in [
        "{bad",
        "{}",
        "{\"bytecode\":\"0xzz\"}",
        "{\"address\":\"0x00\",\"chain\":\"nowhere\"}",
    ] {
        let answer = post(&server, request);
        assert!(answer.starts_with("HTTP/1.1 4"), "{request}: {answer}");
        assert!(
            body(&answer).trim_start().starts_with("{\"error\":"),
            "{request}: {answer}"
        );
    }
}

#[test]
fn text_from_request_headers_does_not_reach_the_page() {
    let server = start();
    let marker = "x\"><script>marker()</script>";
    let page = send(
        &server,
        &format!(
            "GET / HTTP/1.1\r\nHost: {marker}\r\nX-Forwarded-Proto: javascript\r\nConnection: close\r\n\r\n"
        ),
    );
    assert!(
        page.starts_with("HTTP/1.1 200"),
        "{}",
        &page[..page.len().min(200)]
    );
    assert!(!page.contains("marker()"));
    assert!(!page.contains("javascript://"));
}
