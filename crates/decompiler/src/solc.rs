use crate::hex;
use serde_json::{json, Value};
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const RELEASES: &str = "https://binaries.soliditylang.org/linux-amd64";

#[derive(Clone, Debug)]
pub struct Built {
    pub name: String,
    pub compiler: String,
    pub runtime: Vec<u8>,
    pub signatures: HashMap<u32, String>,
}

type Version = (u64, u64, u64);

fn parse_version(text: &str) -> Option<Version> {
    let mut parts = text.trim().trim_start_matches('v').split('.');
    let mut next = || {
        parts.next().and_then(|p| {
            p.trim_matches(|c: char| !c.is_ascii_digit())
                .parse::<u64>()
                .ok()
        })
    };
    let major = next()?;
    Some((major, next().unwrap_or(0), next().unwrap_or(0)))
}

fn satisfies(version: Version, comparator: &str) -> bool {
    let comparator = comparator.trim();
    let split = comparator
        .find(|c: char| c.is_ascii_digit())
        .unwrap_or(comparator.len());
    let (operator, number) = comparator.split_at(split);
    let Some(wanted) = parse_version(number) else {
        return true;
    };
    let dots = number.matches('.').count();
    match operator.trim() {
        ">=" => version >= wanted,
        ">" => version > wanted,
        "<=" => version <= wanted,
        "<" => version < wanted,
        "^" => {
            let ceiling = match wanted {
                (0, 0, patch) => (0, 0, patch + 1),
                (0, minor, _) => (0, minor + 1, 0),
                (major, _, _) => (major + 1, 0, 0),
            };
            version >= wanted && version < ceiling
        }
        "~" => version >= wanted && version < (wanted.0, wanted.1 + 1, 0),
        _ if dots < 2 => (version.0, version.1) == (wanted.0, wanted.1),
        _ => version == wanted,
    }
}

fn pragmas(text: &str) -> Vec<String> {
    let lines = text.lines().map(str::trim);
    let asked = lines.filter_map(|l| l.strip_prefix("pragma solidity"));
    asked
        .map(|rest| rest.trim().trim_end_matches(';').to_string())
        .collect()
}

fn allowed(version: Version, pragma: &str) -> bool {
    pragma.split("||").any(|range| {
        let range = range
            .replace(">= ", ">=")
            .replace("<= ", "<=")
            .replace("> ", ">")
            .replace("< ", "<");
        let range = range.replace(" - ", " <=");
        range.split_whitespace().all(|c| satisfies(version, c))
    })
}

fn cache_dir() -> PathBuf {
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".to_string());
    let dir =
        std::env::var("EVMDEC_SOLC_DIR").unwrap_or_else(|_| format!("{home}/.cache/evmdec/solc"));
    PathBuf::from(dir)
}

fn fetch(url: &str) -> Result<Vec<u8>, String> {
    let response = ureq::get(url).call().map_err(|e| format!("{url}: {e}"))?;
    let mut bytes = Vec::new();
    let mut reader = response.into_reader();
    std::io::Read::read_to_end(&mut reader, &mut bytes).map_err(|e| format!("{url}: {e}"))?;
    Ok(bytes)
}

fn releases() -> Result<BTreeMap<Version, String>, String> {
    let dir = cache_dir();
    let listed = dir.join("list.json");
    if !listed.exists() {
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        let bytes = fetch(&format!("{RELEASES}/list.json"))?;
        std::fs::write(&listed, bytes).map_err(|e| e.to_string())?;
    }
    let text = std::fs::read_to_string(&listed).map_err(|e| e.to_string())?;
    let list: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    let all = list["releases"]
        .as_object()
        .ok_or("the compiler list has no releases")?;
    let known = all
        .iter()
        .filter_map(|(v, path)| Some((parse_version(v)?, path.as_str()?.to_string())));
    Ok(known.collect())
}

// `SOLC` names a compiler to use as it is, for a machine that may not download one.
fn compiler(pragmas: &[String]) -> Result<(PathBuf, String), String> {
    if let Ok(path) = std::env::var("SOLC") {
        return Ok((PathBuf::from(path), "as given".to_string()));
    }
    let known = releases()?;
    let fits = |v: &Version| pragmas.iter().all(|p| allowed(*v, p));
    let (version, path) = known
        .iter()
        .rev()
        .find(|(v, _)| fits(v))
        .ok_or_else(|| format!("no compiler release fits {pragmas:?}"))?;
    let local = cache_dir().join(path);
    if !local.exists() {
        let bytes = fetch(&format!("{RELEASES}/{path}"))?;
        std::fs::write(&local, bytes).map_err(|e| e.to_string())?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::Permissions::from_mode(0o755);
            std::fs::set_permissions(&local, mode).map_err(|e| e.to_string())?;
        }
    }
    Ok((local, format!("{}.{}.{}", version.0, version.1, version.2)))
}

fn run(solc: &Path, input: &Value) -> Result<Value, String> {
    let mut child = Command::new(solc)
        .arg("--standard-json")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("{}: {e}", solc.display()))?;
    let text = input.to_string();
    let mut stdin = child.stdin.take().ok_or("the compiler takes no input")?;
    // Written from another thread. A large input would fill the pipe while the compiler
    // waits for its own output to be read.
    std::thread::spawn(move || {
        let _ = std::io::Write::write_all(&mut stdin, text.as_bytes());
    });
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    serde_json::from_slice(&out.stdout)
        .map_err(|e| format!("the compiler's answer was not read: {e}"))
}

// The optimizer refuses a source that reads the size of memory, so a refusal is tried
// again without it.
pub fn compile(source: &str) -> Result<Vec<Built>, String> {
    let built = compile_with(source, true).or_else(|_| compile_with(source, false));
    built.map_err(|refused| refused.message)
}

#[derive(Clone, Debug, Default)]
pub struct Refusal {
    pub message: String,
    pub places: Vec<usize>,
}

impl From<String> for Refusal {
    fn from(message: String) -> Refusal {
        Refusal {
            message,
            places: Vec::new(),
        }
    }
}

pub fn compile_with(source: &str, optimize: bool) -> Result<Vec<Built>, Refusal> {
    let (solc, compiler) = compiler(&pragmas(source))?;
    let input = json!({
        "language": "Solidity",
        "sources": {"contract.sol": {"content": source}},
        "settings": {
            "optimizer": {"enabled": optimize, "runs": 200},
            "outputSelection": {"*": {"*": [
                "evm.deployedBytecode.object", "evm.methodIdentifiers"
            ]}}
        }
    });
    let out = run(&solc, &input)?;
    let failed = |e: &&Value| e["severity"] == "error";
    let errors: Vec<&Value> = out["errors"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(failed)
        .collect();
    if let Some(error) = errors.first() {
        let said = error["formattedMessage"]
            .as_str()
            .or(error["message"].as_str());
        let starts = errors
            .iter()
            .filter_map(|e| e["sourceLocation"]["start"].as_u64());
        return Err(Refusal {
            message: said
                .unwrap_or("the compiler reported an error")
                .trim()
                .to_string(),
            places: starts.map(|at| at as usize).collect(),
        });
    }
    let mut found = Vec::new();
    let files = out["contracts"].as_object().into_iter().flatten();
    for (name, built) in files.flat_map(|(_, c)| c.as_object().into_iter().flatten()) {
        let object = built["evm"]["deployedBytecode"]["object"]
            .as_str()
            .unwrap_or("");
        // An unlinked library leaves a placeholder that is not hex. Such code cannot be run.
        let Ok(runtime) = hex::decode(object) else {
            continue;
        };
        if runtime.is_empty() {
            continue;
        }
        let listed = built["evm"]["methodIdentifiers"].as_object();
        let signatures = listed
            .into_iter()
            .flatten()
            .filter_map(|(signature, selector)| {
                let selector = u32::from_str_radix(selector.as_str()?, 16).ok()?;
                Some((selector, signature.clone()))
            });
        found.push(Built {
            name: name.clone(),
            compiler: compiler.clone(),
            runtime,
            signatures: signatures.collect(),
        });
    }
    match found.is_empty() {
        true => Err("the source holds no contract that can be deployed"
            .to_string()
            .into()),
        false => Ok(found),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_pragma_picks_the_versions_it_allows() {
        assert!(allowed((0, 8, 19), "^0.8.4"));
        assert!(!allowed((0, 9, 0), "^0.8.4"));
        assert!(allowed((0, 6, 12), ">=0.6.0 <0.8.0"));
        assert!(!allowed((0, 8, 0), ">=0.6.0 <0.8.0"));
        assert!(allowed((0, 4, 24), "0.4.24"));
        assert!(allowed((0, 5, 17), "^0.5.0 || ^0.6.0"));
        assert!(allowed((0, 4, 26), "~0.4.11"));
    }
}
