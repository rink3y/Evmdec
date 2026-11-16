use evmdec::hex;
use serde_json::{json, Value};
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const RELEASES: &str = "https://binaries.soliditylang.org/linux-amd64";

// One contract as the compiler produced it, with what is needed to point back at its source.
#[derive(Clone, Debug)]
pub struct Compiled {
    pub name: String,
    pub file: String,
    pub compiler: String,
    pub runtime: Vec<u8>,
    pub creation: Vec<u8>,
    // Selector to signature, as the compiler lists them.
    pub names: HashMap<u32, String>,
    pub source_map: String,
    // Source texts in the order the source map numbers them.
    pub sources: Vec<(String, String)>,
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

// Whether a version satisfies one comparator of a pragma, such as `^0.8.4` or `>=0.6.0`.
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
    let mut found = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("pragma solidity") {
            found.push(rest.trim().trim_end_matches(';').to_string());
        }
    }
    found
}

fn allowed(version: Version, pragma: &str) -> bool {
    // Alternatives are joined by `||`. Within one, every comparator has to hold.
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

/* The compiler a source asks for: the newest release every pragma allows, or the one
named outright. It is fetched once and kept. `SOLC` names a compiler to use as it is. */
fn compiler(pragmas: &[String], named: Option<&str>) -> Result<(PathBuf, String), String> {
    if let Ok(path) = std::env::var("SOLC") {
        return Ok((PathBuf::from(path), "as given".to_string()));
    }
    let known = releases()?;
    let wanted = named.and_then(parse_version);
    let fits = |v: &Version| match wanted {
        Some(exact) => *v == exact,
        None => pragmas.iter().all(|p| allowed(*v, p)),
    };
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

// A file and everything it imports by a path relative to itself.
fn gather(root: &Path, name: &str, into: &mut BTreeMap<String, String>) -> Result<(), String> {
    if into.contains_key(name) {
        return Ok(());
    }
    let path = root.join(name);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    into.insert(name.to_string(), text.clone());
    for line in text
        .lines()
        .map(str::trim)
        .filter(|l| l.starts_with("import"))
    {
        let quoted = line.split(['"', '\'']).nth(1);
        let Some(target) = quoted.filter(|t| t.starts_with('.')) else {
            continue;
        };
        let from = Path::new(name).parent().unwrap_or(Path::new(""));
        let mut joined = PathBuf::new();
        for part in from.join(target).components() {
            match part {
                std::path::Component::ParentDir => {
                    joined.pop();
                }
                std::path::Component::CurDir => {}
                other => joined.push(other),
            }
        }
        gather(root, &joined.to_string_lossy(), into)?;
    }
    Ok(())
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
    std::thread::spawn(move || {
        let _ = std::io::Write::write_all(&mut stdin, text.as_bytes());
    });
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    serde_json::from_slice(&out.stdout)
        .map_err(|e| format!("the compiler's answer was not read: {e}"))
}

/* Compiles a standard JSON input, the form verified sources are published in. The
settings are kept as given, apart from asking for the outputs needed here. */
pub fn compile_input(mut input: Value, version: Option<&str>) -> Result<Vec<Compiled>, String> {
    let texts: Vec<String> = input["sources"]
        .as_object()
        .into_iter()
        .flatten()
        .filter_map(|(_, s)| s["content"].as_str().map(str::to_string))
        .collect();
    let asked: Vec<String> = texts.iter().flat_map(|t| pragmas(t)).collect();
    let (solc, compiler) = compiler(&asked, version)?;
    input["settings"]["outputSelection"] = json!({"*": {"*": [
        "evm.bytecode.object", "evm.deployedBytecode.object",
        "evm.deployedBytecode.sourceMap", "evm.methodIdentifiers"
    ]}});
    let out = run(&solc, &input)?;
    let failed = |e: &&Value| e["severity"] == "error";
    if let Some(error) = out["errors"].as_array().into_iter().flatten().find(failed) {
        let said = error["formattedMessage"]
            .as_str()
            .or(error["message"].as_str());
        return Err(said
            .unwrap_or("the compiler reported an error")
            .trim()
            .to_string());
    }
    let mut numbered: Vec<(u64, String)> = out["sources"]
        .as_object()
        .into_iter()
        .flatten()
        .map(|(file, s)| (s["id"].as_u64().unwrap_or(0), file.clone()))
        .collect();
    numbered.sort();
    let text_of = |file: &str| {
        input["sources"][file]["content"]
            .as_str()
            .unwrap_or("")
            .to_string()
    };
    let sources: Vec<(String, String)> = numbered
        .into_iter()
        .map(|(_, f)| (f.clone(), text_of(&f)))
        .collect();
    let mut found = Vec::new();
    for (file, contracts) in out["contracts"].as_object().into_iter().flatten() {
        for (name, built) in contracts.as_object().into_iter().flatten() {
            let object = |path: &str| built["evm"][path]["object"].as_str().unwrap_or("");
            // An unlinked library leaves a placeholder that is not hex. Such code cannot be run.
            let (Ok(runtime), Ok(creation)) = (
                hex::decode(object("deployedBytecode")),
                hex::decode(object("bytecode")),
            ) else {
                continue;
            };
            if runtime.is_empty() {
                continue;
            }
            let listed = built["evm"]["methodIdentifiers"].as_object();
            let names = listed
                .into_iter()
                .flatten()
                .filter_map(|(signature, selector)| {
                    let selector = u32::from_str_radix(selector.as_str()?, 16).ok()?;
                    Some((selector, signature.clone()))
                });
            found.push(Compiled {
                name: name.clone(),
                file: file.clone(),
                compiler: compiler.clone(),
                runtime,
                creation,
                names: names.collect(),
                source_map: built["evm"]["deployedBytecode"]["sourceMap"]
                    .as_str()
                    .unwrap_or("")
                    .to_string(),
                sources: sources.clone(),
            });
        }
    }
    match found.is_empty() {
        true => Err("the source holds no contract that can be deployed".to_string()),
        false => Ok(found),
    }
}

// Compiles one Solidity file with the files it imports by relative path.
pub fn compile_file(path: &Path) -> Result<Vec<Compiled>, String> {
    let root = path.parent().unwrap_or(Path::new("."));
    let name = path
        .file_name()
        .ok_or("not a file")?
        .to_string_lossy()
        .to_string();
    let mut texts = BTreeMap::new();
    gather(root, &name, &mut texts)?;
    let sources: serde_json::Map<String, Value> = texts
        .into_iter()
        .map(|(file, content)| (file, json!({ "content": content })))
        .collect();
    let input = json!({
        "language": "Solidity",
        "sources": sources,
        "settings": {"optimizer": {"enabled": true, "runs": 200}}
    });
    compile_input(input, None)
}

impl Compiled {
    /* The line of source an instruction came from. The source map gives one entry per
    instruction, each field empty where it repeats the entry before. */
    #[must_use]
    pub fn line_of(&self, pc: usize) -> Option<String> {
        let index = evmdec::disasm::disassemble(&self.runtime)
            .iter()
            .position(|i| i.pc == pc)?;
        let (mut start, mut file) = (0usize, 0i64);
        for (n, entry) in self.source_map.split(';').enumerate() {
            let mut fields = entry.split(':');
            if let Some(s) = fields.next().and_then(|f| f.parse().ok()) {
                start = s;
            }
            let _length = fields.next();
            if let Some(f) = fields.next().and_then(|f| f.parse().ok()) {
                file = f;
            }
            if n == index {
                break;
            }
        }
        let (name, text) = self.sources.get(usize::try_from(file).ok()?)?;
        let line = text.get(..start)?.matches('\n').count() + 1;
        Some(format!("{name}:{line}"))
    }

    // Where a function is declared, for a finding that names a function and no instruction.
    #[must_use]
    pub fn declared_at(&self, function: &str) -> Option<String> {
        let name = function.split('(').next()?;
        let needle = format!("function {name}");
        for (file, text) in &self.sources {
            for (n, line) in text.lines().enumerate() {
                let rest = line.trim_start().strip_prefix(&needle);
                if rest.is_some_and(|r| r.trim_start().starts_with('(')) {
                    return Some(format!("{file}:{}", n + 1));
                }
            }
        }
        None
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
