use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use evmdec::decompile::{Contract, Options};
use evmdec::fetch::{CodeCache, Policy};
use evmdec::rpc::Client;
use std::collections::BTreeMap;
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "evmdec",
    version,
    about = "EVM bytecode decompiler and security analyzer"
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Show bytecode facts: kind, size, compiler metadata.
    Info { file: PathBuf },
    /// Linear disassembly.
    Disasm { file: PathBuf },
    /// Control-flow recovery statistics.
    Cfg { file: PathBuf },
    /// Decompile to pseudo-Solidity. INPUT is a file (binary or hex), a hex string, or a 0x address.
    Decompile {
        input: String,
        /// JSON-RPC endpoint(s), comma-separated (default: public endpoints of --chain, or $EVMDEC_RPC_URL).
        #[arg(long)]
        rpc: Option<String>,
        /// Chain name or id for address lookups.
        #[arg(long, default_value = "mainnet")]
        chain: String,
        /// Do not resolve and decompile the implementation behind a proxy.
        #[arg(long)]
        no_follow_proxy: bool,
        /// Labels and gotos instead of structured code.
        #[arg(long)]
        flat: bool,
        /// JSON output with all facts.
        #[arg(long)]
        json: bool,
        /// Also decompile embedded contracts (CREATE/CREATE2 payloads).
        #[arg(long)]
        embedded: bool,
        /// Disable the built-in signature dictionary.
        #[arg(long)]
        no_sigs: bool,
        /// Append the security report (markdown) after the code.
        #[arg(long)]
        report: bool,
        /// Resolve unknown selectors online (openchain.xyz, 4byte.directory).
        #[arg(long)]
        lookup: bool,
    },
    /// Block-level oracle: execute every basic block concretely and through the lifted IR.
    Verify {
        file: PathBuf,
        /// Random states per block.
        #[arg(long, default_value_t = 8)]
        runs: usize,
        #[arg(long, default_value_t = 1)]
        seed: u64,
        #[arg(long)]
        verbose: bool,
        #[arg(long)]
        json: bool,
    },
    /// Security analysis report (markdown, or JSON with --json).
    Analyze {
        file: PathBuf,
        #[arg(long)]
        json: bool,
    },
    /// Look up selectors (8 hex digits) or event topics (64 hex digits) in the signature
    /// dictionary and the local index; with no argument, report which index is in use.
    Sigs {
        /// 4-byte selectors or 32-byte topic hashes, with or without 0x.
        hashes: Vec<String>,
    },
}

fn load(file: &PathBuf) -> Result<Vec<u8>> {
    let raw = std::fs::read(file).with_context(|| format!("reading {}", file.display()))?;
    if raw.iter().all(|b| b.is_ascii()) {
        let s = String::from_utf8_lossy(&raw);
        let t = s.trim();
        if t.starts_with("0x") || t.chars().all(|c| c.is_ascii_hexdigit()) {
            return evmdec::hex::decode(t).map_err(|e| anyhow::anyhow!(e));
        }
    }
    Ok(raw)
}

/// A file path, or a hex string given directly on the command line.
fn load_input(input: &str) -> Result<Vec<u8>> {
    let p = PathBuf::from(input);
    if p.exists() {
        return load(&p);
    }
    let t = input.trim();
    if t.starts_with("0x") || (t.len() > 8 && t.chars().all(|c| c.is_ascii_hexdigit())) {
        return evmdec::hex::decode(t).map_err(|e| anyhow::anyhow!(e));
    }
    anyhow::bail!("'{}' is neither a file, a hex string nor an address", input)
}

/// Fetch the contract at `address` on `chain` and, under `policy`, resolve and compose it with
/// the code it forwards to. Progress goes to stderr.
fn fetch_and_decompile(
    address: &str,
    rpc: Option<&str>,
    chain: &str,
    policy: Policy,
    opts: &Options,
) -> Result<Contract> {
    let client = Client::new(rpc, chain).map_err(|e| anyhow::anyhow!(e))?;
    let mut cache = CodeCache::new();
    evmdec::fetch::fetch(
        &client,
        address,
        chain,
        opts,
        policy,
        &mut cache,
        &mut |line| eprintln!("{}", line),
    )
    .map_err(|e| anyhow::anyhow!(e))
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Info { file } => {
            let code = load(&file)?;
            let info = evmdec::metadata::analyze(&code);
            println!("{}", serde_json::to_string_pretty(&info)?);
        }
        Cmd::Cfg { file } => {
            let code = load(&file)?;
            let info = evmdec::metadata::analyze(&code);
            let t = std::time::Instant::now();
            let prog = evmdec::cfg::Program::new(info.runtime.clone());
            let code_end = info
                .metadata
                .as_ref()
                .map(|m| m.offset)
                .unwrap_or(prog.code.len());
            let rec = evmdec::cfg::recover(&prog, code_end);
            let total_nodes: usize = rec.main.nodes.len()
                + rec.functions.values().map(|u| u.nodes.len()).sum::<usize>()
                + rec.orphans.values().map(|u| u.nodes.len()).sum::<usize>();
            let code_blocks = prog.blocks.iter().filter(|b| b.start < code_end).count();
            println!("blocks={} code_blocks={} main_nodes={} functions={} orphans={} total_nodes={} unresolved_jumps={} budget_exhausted={} time={:?}",
                prog.blocks.len(), code_blocks, rec.main.nodes.len(), rec.functions.len(), rec.orphans.len(), total_nodes, rec.unresolved_jumps.len(), rec.budget_exhausted, t.elapsed());
            for pc in &rec.unresolved_jumps {
                println!("  unresolved jump ending at {:#x}", pc);
            }
            if let Ok(v) = std::env::var("EVMDEC_SUMMARY") {
                let an = evmdec::cfg::Analysis::new(&prog);
                for pcs in v.split(',') {
                    let pc = usize::from_str_radix(pcs.trim_start_matches("0x"), 16)?;
                    let b = prog.block_at_pc[&pc];
                    let s = an.summary(b);
                    println!(
                        "  summary {:#x}: exits={:?} may_halt={} unresolved={} blocks={}",
                        pc,
                        s.exits,
                        s.may_halt,
                        s.unresolved,
                        s.blocks.len()
                    );
                }
            }
            if std::env::var("EVMDEC_CTX").is_ok() {
                let mut per: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
                for n in &rec.main.nodes {
                    per.entry(n.block).or_default().push(n.id);
                }
                let mut v: Vec<(usize, usize)> = per.iter().map(|(b, v)| (v.len(), *b)).collect();
                v.sort_unstable_by(|a, b| b.cmp(a));
                for (cnt, b) in v.iter().take(5) {
                    println!("  main block {:#x} nodes={}", prog.blocks[*b].start, cnt);
                    for id in per[b].iter().take(5) {
                        let n = &rec.main.nodes[*id];
                        println!(
                            "     {:?} preds={:?}",
                            n.entry,
                            n.preds
                                .iter()
                                .map(|p| format!(
                                    "{:#x}",
                                    prog.blocks[rec.main.nodes[*p].block].start
                                ))
                                .collect::<Vec<_>>()
                        );
                    }
                }
            }
            if std::env::var("EVMDEC_DEBUG").is_ok() {
                for (f, u) in &rec.functions {
                    let calls = u.nodes.iter().filter(|n| n.call.is_some()).count();
                    let rets: Vec<String> = u
                        .nodes
                        .iter()
                        .filter_map(|n| n.returns_via.map(|v| format!("{:?}", v)))
                        .collect();
                    let unres: Vec<String> = u
                        .nodes
                        .iter()
                        .filter(|n| n.unresolved)
                        .map(|n| format!("{:#x}", prog.blocks[n.block].end))
                        .collect();
                    println!(
                        "  function {:#x}: nodes={} calls={} returns_via={:?} unresolved={:?}",
                        prog.blocks[*f].start,
                        u.nodes.len(),
                        calls,
                        rets.iter().take(3).collect::<Vec<_>>(),
                        unres
                    );
                }
                for (b, u) in &rec.orphans {
                    let unres: Vec<String> = u
                        .nodes
                        .iter()
                        .filter(|n| n.unresolved)
                        .map(|n| format!("{:#x}", prog.blocks[n.block].end))
                        .collect();
                    if !unres.is_empty() || u.nodes.len() > 1 {
                        println!(
                            "  orphan {:#x}: nodes={} unresolved={:?}",
                            prog.blocks[*b].start,
                            u.nodes.len(),
                            unres
                        );
                    }
                }
                let unres: Vec<String> = rec
                    .main
                    .nodes
                    .iter()
                    .filter(|n| n.unresolved)
                    .map(|n| format!("{:#x}", prog.blocks[n.block].end))
                    .collect();
                println!("  main unresolved={:?}", unres);
            }
        }
        Cmd::Decompile {
            input,
            rpc,
            chain,
            no_follow_proxy,
            flat,
            json,
            embedded,
            no_sigs,
            report,
            lookup,
        } => {
            let mut opts = Options {
                flat,
                pcs: false,
                embedded,
                no_sigs,
                extra_sigs: Default::default(),
            };
            let file = PathBuf::from(&input);
            let is_addr = evmdec::rpc::is_address(&input);
            let code = if is_addr {
                None
            } else {
                Some(load_input(&input)?)
            };
            if lookup {
                // First pass to learn the selectors, then resolve the unknown ones online.
                let probe = code
                    .as_ref()
                    .map(|c| evmdec::decompile::decompile(c, &opts));
                if let Some(pc) = probe {
                    let sels: Vec<u32> = pc
                        .functions
                        .iter()
                        .filter(|f| f.signature.is_none())
                        .filter_map(|f| f.selector.as_ref())
                        .filter_map(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok())
                        .collect();
                    opts.extra_sigs = evmdec::sigs::lookup_online(&sels);
                    eprintln!(
                        "resolved {} of {} unknown selectors online",
                        opts.extra_sigs.len(),
                        sels.len()
                    );
                }
            }
            let c = match code {
                None => fetch_and_decompile(
                    &input,
                    rpc.as_deref(),
                    &chain,
                    Policy {
                        follow: !no_follow_proxy,
                        ..Policy::default()
                    },
                    &opts,
                )?,
                Some(code) => {
                    let opts2 = opts.clone();
                    // Defense in depth only: the decompiler is written to never panic (the
                    // corpus and oracle runs check that), so this guard is never relied upon.
                    // When it does fire, the user still gets a disassembly instead of nothing.
                    match std::panic::catch_unwind(move || {
                        evmdec::decompile::decompile(&code, &opts2)
                    }) {
                        Ok(c) => c,
                        Err(_) => {
                            eprintln!("internal error while decompiling; printing the disassembly instead (please report this bytecode)");
                            let code = load_input(&input)?;
                            let info = evmdec::metadata::analyze(&code);
                            for i in evmdec::disasm::disassemble(&info.runtime) {
                                println!("{}", evmdec::disasm::format_instruction(&i));
                            }
                            return Ok(());
                        }
                    }
                }
            };
            if json {
                let r = evmdec::analyze::analyze(&c);
                let mut v = serde_json::to_value(&c)?;
                v["report"] = serde_json::to_value(&r)?;
                println!("{}", serde_json::to_string_pretty(&v)?);
            } else {
                print!("{}", c.source);
                if report {
                    let r = evmdec::analyze::analyze(&c);
                    println!(
                        "\n/*\n{}*/",
                        evmdec::analyze::render_markdown(&c, &r, &file.display().to_string())
                    );
                    if let Some(p) = &c.proxy {
                        if let Some(ic) = &p.contract {
                            let r2 = evmdec::analyze::analyze(ic);
                            println!(
                                "\n/*\n{}*/",
                                evmdec::analyze::render_markdown(
                                    ic,
                                    &r2,
                                    &format!("implementation {}", p.implementation)
                                )
                            );
                        }
                    }
                    for lc in &c.linked {
                        let lr = evmdec::analyze::analyze(lc);
                        println!(
                            "\n/*\n{}*/",
                            evmdec::analyze::render_markdown(
                                lc,
                                &lr,
                                &format!(
                                    "linked contract {}",
                                    lc.address.as_deref().unwrap_or("?")
                                )
                            )
                        );
                    }
                }
            }
        }
        Cmd::Verify {
            file,
            runs,
            seed,
            verbose,
            json,
        } => {
            let code = load(&file)?;
            let info = evmdec::metadata::analyze(&code);
            let st = evmdec::verify::verify(
                &info.runtime,
                &evmdec::verify::VerifyOptions {
                    runs,
                    seed,
                    verbose,
                },
            );
            if json {
                println!("{}", serde_json::to_string_pretty(&st)?);
            } else {
                println!(
                    "blocks={} runs={} agree={} mismatch={} inconclusive={}",
                    st.blocks, st.runs, st.agree, st.mismatch, st.inconclusive
                );
                println!("blocks verified={} mismatched={} inconclusive={}; instructions verified {}/{} ({:.3}%)", st.blocks_verified, st.blocks_mismatched, st.blocks_inconclusive, st.instructions_verified, st.instructions_total, 100.0 * st.instructions_verified as f64 / st.instructions_total.max(1) as f64);
                let mut reasons: Vec<(&String, &usize)> = st.inconclusive_reasons.iter().collect();
                reasons.sort_by(|a, b| b.1.cmp(a.1));
                for (r, n) in reasons.iter().take(8) {
                    println!("  inconclusive: {} x{}", r, n);
                }
                for m in st.mismatches.iter().take(20) {
                    println!("  {}", m);
                }
            }
        }
        Cmd::Sigs { hashes } => {
            if hashes.is_empty() {
                match evmdec::sigdb::global() {
                    Some(db) => println!("local index: {} signatures", db.len()),
                    None => println!(
                        "local index: none (set EVMDEC_SIGS or install sigs.idx; see corpus/build_sigs.py)"
                    ),
                }
            }
            for h in &hashes {
                let hex = h.trim().trim_start_matches("0x");
                let line = match hex.len() {
                    8 => {
                        let sel = u32::from_str_radix(hex, 16)
                            .with_context(|| format!("bad selector {h}"))?;
                        let mut names: Vec<String> = Vec::new();
                        if let Some(s) = evmdec::sigs::function(sel) {
                            names.push(s.into_owned());
                        }
                        if let Some(s) = evmdec::sigs::error(sel) {
                            if !names.iter().any(|n| n == &*s) {
                                names.push(s.into_owned());
                            }
                        }
                        if let Some(db) = evmdec::sigdb::global() {
                            for s in db.selector(sel) {
                                if !names.contains(&s) {
                                    names.push(s);
                                }
                            }
                        }
                        names.join(" | ")
                    }
                    64 => {
                        let bytes = evmdec::hex::decode(hex).map_err(|e| anyhow::anyhow!(e))?;
                        let topic: [u8; 32] = bytes[..]
                            .try_into()
                            .expect("64 hex digits decode to 32 bytes");
                        evmdec::sigs::event(&topic)
                            .map(|s| s.into_owned())
                            .unwrap_or_default()
                    }
                    _ => anyhow::bail!("'{h}' is neither a 4-byte selector nor a 32-byte topic"),
                };
                println!("0x{hex} {}", if line.is_empty() { "?" } else { &line });
            }
        }
        Cmd::Analyze { file, json } => {
            let code = load(&file)?;
            let c = evmdec::decompile::decompile(&code, &Options::default());
            let r = evmdec::analyze::analyze(&c);
            if json {
                println!("{}", serde_json::to_string_pretty(&r)?);
            } else {
                print!(
                    "{}",
                    evmdec::analyze::render_markdown(&c, &r, &file.display().to_string())
                );
            }
        }
        Cmd::Disasm { file } => {
            let code = load(&file)?;
            let info = evmdec::metadata::analyze(&code);
            for i in evmdec::disasm::disassemble(&info.runtime) {
                println!("{}", evmdec::disasm::format_instruction(&i));
            }
        }
    }
    Ok(())
}
