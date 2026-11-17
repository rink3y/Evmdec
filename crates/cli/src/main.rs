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
    #[command(about = "Show bytecode facts: kind, size, compiler metadata")]
    Info { file: PathBuf },
    #[command(about = "Linear disassembly")]
    Disasm { file: PathBuf },
    #[command(about = "Control-flow recovery statistics")]
    Cfg { file: PathBuf },
    #[command(
        about = "Decompile to pseudo-Solidity. INPUT is a file (binary or hex), a hex string, or a 0x address"
    )]
    Decompile {
        input: String,
        #[arg(
            long,
            help = "JSON-RPC endpoint(s), comma-separated (default: public endpoints of --chain, or $EVMDEC_RPC_URL)"
        )]
        rpc: Option<String>,
        #[arg(
            long,
            default_value = "mainnet",
            help = "Chain name or id for address lookups"
        )]
        chain: String,
        #[arg(
            long,
            help = "Do not resolve and decompile the implementation behind a proxy"
        )]
        no_follow_proxy: bool,
        #[arg(
            long,
            default_value_t = 2,
            help = "Call edges to follow from the contract: 1 fetches what it calls, 2 also what those contracts call. At most 3; 0 fetches no dependency"
        )]
        depth: usize,
        #[arg(long, help = "Labels and gotos instead of structured code")]
        flat: bool,
        #[arg(long, help = "JSON output with all facts")]
        json: bool,
        #[arg(
            long,
            help = "Also decompile embedded contracts (CREATE/CREATE2 payloads)"
        )]
        embedded: bool,
        #[arg(long, help = "Disable the built-in signature dictionary")]
        no_sigs: bool,
        #[arg(long, help = "Append the audit report (markdown) after the code")]
        report: bool,
        #[arg(
            long,
            help = "Resolve unknown selectors online (openchain.xyz, 4byte.directory)"
        )]
        lookup: bool,
    },
    #[command(
        about = "Block-level oracle: execute every basic block concretely and through the lifted IR"
    )]
    Verify {
        file: PathBuf,
        #[arg(long, default_value_t = 8, help = "Random states per block")]
        runs: usize,
        #[arg(long, default_value_t = 1)]
        seed: u64,
        #[arg(long)]
        verbose: bool,
        #[arg(long)]
        json: bool,
    },
    #[command(
        about = "Audit report from running the code (markdown, or JSON with --json). Takes bytecode, a Solidity file, or a compiler's standard JSON input"
    )]
    Audit {
        #[arg(help = "A file, or a 0x address to run on the state its chain holds for it")]
        file: PathBuf,
        #[arg(long)]
        json: bool,
        #[arg(
            long,
            default_value = "mainnet",
            help = "Chain name or id, for an address"
        )]
        chain: String,
        #[arg(
            long,
            help = "Block whose state an address is run on. The newest when left out"
        )]
        block: Option<u64>,
    },
    #[command(
        about = "Look up selectors (8 hex digits) or event topics (64 hex digits) in the signature dictionary and the local index; with no argument, report which index is in use"
    )]
    Sigs {
        #[arg(help = "4-byte selectors or 32-byte topic hashes, with or without 0x")]
        hashes: Vec<String>,
    },
}

fn load(file: &PathBuf) -> Result<Vec<u8>> {
    let raw = std::fs::read(file).with_context(|| format!("reading {}", file.display()))?;
    // Hex is often folded into lines. Read as raw bytes, the line ends and digits would
    // decompile into a report about code that is not there.
    let text: Option<String> = raw.is_ascii().then(|| {
        let text = String::from_utf8_lossy(&raw);
        text.split_ascii_whitespace().collect()
    });
    let hex = text.filter(|t| t.starts_with("0x") || t.chars().all(|c| c.is_ascii_hexdigit()));
    let code = match hex {
        Some(hex) => evmdec::hex::decode(&hex).map_err(|e| anyhow::anyhow!(e))?,
        None => raw,
    };
    if code.is_empty() {
        anyhow::bail!("{} holds no code", file.display());
    }
    Ok(code)
}

fn look_up(c: &Contract) -> std::collections::HashMap<u32, String> {
    let selectors = c.unknown_selectors();
    let found = evmdec::sigs::lookup_online(&selectors);
    eprintln!(
        "resolved {} of {} unknown selectors online",
        found.len(),
        selectors.len()
    );
    found
}

// Output piped into a command that stops reading, such as head, is not a failure.
fn quiet_on_closed_pipe() {
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let text = info.payload().downcast_ref::<String>();
        if text.is_some_and(|t| t.starts_with("failed printing to stdout")) {
            std::process::exit(0);
        }
        default(info);
    }));
}

fn load_input(input: &str) -> Result<Vec<u8>> {
    let p = PathBuf::from(input);
    if p.exists() {
        return load(&p);
    }
    let t = input.trim();
    if t.starts_with("0x") || (t.len() > 8 && t.chars().all(|c| c.is_ascii_hexdigit())) {
        let code = evmdec::hex::decode(t).map_err(|e| anyhow::anyhow!(e))?;
        if code.is_empty() {
            anyhow::bail!("'{input}' holds no code");
        }
        return Ok(code);
    }
    anyhow::bail!("'{}' is neither a file, a hex string nor an address", input)
}

fn fetch_and_decompile(
    address: &str,
    rpc: Option<&str>,
    chain: &str,
    policy: Policy,
    opts: &mut Options,
    lookup: bool,
) -> Result<Contract> {
    let client = Client::new(rpc, chain).map_err(|e| anyhow::anyhow!(e))?;
    let mut cache = CodeCache::new();
    let mut fetch = |opts: &Options| {
        let mut log = |line: &str| eprintln!("{line}");
        evmdec::fetch::fetch(&client, address, chain, opts, policy, &mut cache, &mut log)
            .map_err(|e| anyhow::anyhow!(e))
    };
    let c = fetch(opts)?;
    if !lookup {
        return Ok(c);
    }
    // The names can only be asked for once the code is here. The second pass reads the
    // code from the cache and uses them.
    opts.extra_sigs = look_up(&c);
    if opts.extra_sigs.is_empty() {
        return Ok(c);
    }
    fetch(opts)
}

fn audit_address(address: &str, chain: &str, block: Option<u64>) -> Result<audit::Report> {
    let fetch = |client: &Client| {
        let mut log = |line: &str| eprintln!("{line}");
        let policy = Policy {
            depth: 0,
            ..Policy::default()
        };
        let options = Options::default();
        let mut cache = CodeCache::new();
        evmdec::fetch::fetch(
            client, address, chain, &options, policy, &mut cache, &mut log,
        )
        .map_err(|e| anyhow::anyhow!(e))
    };
    let connect = || Client::new(None, chain);
    let fixed = connect().and_then(|client| {
        let (client, number, time) = client.at(block)?;
        client.get_code(address)?;
        Ok((client, number, time))
    });
    match fixed {
        Ok((client, number, time)) => {
            let mut c = fetch(&client)?;
            // Decompiling took time out of what one client may spend on the network.
            let fresh = || {
                let at = connect().and_then(|client| client.at(Some(number)));
                at.map(|(client, ..)| client)
                    .map_err(|e| anyhow::anyhow!(e))
            };
            let node = std::rc::Rc::new(audit::chain::Node::new(fresh()?));
            if let Some(behind) = audit::handed_to(&c, node, number, time) {
                let behind = evmdec::rpc::addr_to_string(behind);
                eprintln!("every call is handed to the code at {behind}: auditing that code on this contract's state");
                let code = fresh()?.get_code(&behind).map_err(|e| anyhow::anyhow!(e))?;
                let mut inner = evmdec::decompile::decompile(&code, &Options::default());
                inner.address.clone_from(&c.address);
                inner.chain.clone_from(&c.chain);
                c = inner;
            }
            Ok(audit::audit_at(&c, fresh()?, chain, number, time))
        }
        Err(why) => {
            let client = connect().map_err(|e| anyhow::anyhow!(e))?;
            let c = fetch(&client)?;
            let mut report = audit::audit(&c);
            let at = block.map_or("its newest block".to_string(), |n| format!("block {n}"));
            report.state.push(format!(
                "The state of {chain} at {at} could not be read: {why}. The contract was run in a world guessed from its code alone."
            ));
            Ok(report)
        }
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    quiet_on_closed_pipe();
    match evmdec::clock::on_worker(|| run(cli)) {
        Ok(done) => done,
        Err(panic) => std::panic::resume_unwind(panic),
    }
}

fn run(cli: Cli) -> Result<()> {
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
        }
        Cmd::Decompile {
            input,
            rpc,
            chain,
            no_follow_proxy,
            depth,
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
            let is_addr = evmdec::rpc::is_address(&input);
            let code = if is_addr {
                None
            } else {
                Some(load_input(&input)?)
            };
            if let (true, Some(code)) = (lookup, &code) {
                opts.extra_sigs = look_up(&evmdec::decompile::decompile(code, &opts));
            }
            let c = match code {
                None => fetch_and_decompile(
                    &input,
                    rpc.as_deref(),
                    &chain,
                    Policy {
                        follow: !no_follow_proxy,
                        depth: depth.min(3),
                        ..Policy::default()
                    },
                    &mut opts,
                    lookup,
                )?,
                Some(code) => {
                    let opts2 = opts.clone();
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
                            anyhow::bail!("the decompiler failed on this input");
                        }
                    }
                }
            };
            if json {
                let mut v = serde_json::to_value(&c)?;
                v["report"] = serde_json::to_value(audit::audit_all(&c))?;
                println!("{}", serde_json::to_string_pretty(&v)?);
            } else {
                print!("{}", c.source);
                if report {
                    println!("\n/*\n{}*/", audit::markdown(&audit::audit_all(&c)));
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
        Cmd::Audit {
            file,
            json,
            chain,
            block,
        } => {
            let address = file.to_str().filter(|s| evmdec::rpc::is_address(s));
            if let Some(address) = address {
                let report = audit_address(address, &chain, block)?;
                if json {
                    println!("{}", serde_json::to_string_pretty(&report)?);
                } else {
                    print!("{}", audit::markdown(&report));
                }
                return Ok(());
            }
            let kind = file.extension().and_then(|e| e.to_str()).unwrap_or("");
            if kind == "sol" || kind == "json" {
                let built = match kind {
                    "sol" => audit::source::compile_file(&file),
                    _ => {
                        let text = std::fs::read_to_string(&file)?;
                        audit::source::compile_input(serde_json::from_str(&text)?, None)
                    }
                };
                let built = built.map_err(|e| anyhow::anyhow!(e))?;
                let reports: Vec<audit::Report> = built.iter().map(audit::audit_compiled).collect();
                if json {
                    println!("{}", serde_json::to_string_pretty(&reports)?);
                } else {
                    for report in &reports {
                        print!("{}", audit::markdown(report));
                    }
                }
                return Ok(());
            }
            let code = load(&file)?;
            let c = evmdec::decompile::decompile(&code, &Options::default());
            let r = audit::audit(&c);
            if json {
                println!("{}", serde_json::to_string_pretty(&r)?);
            } else {
                print!("{}", audit::markdown(&r));
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
