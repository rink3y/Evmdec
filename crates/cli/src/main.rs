use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use std::path::PathBuf;
#[allow(unused_imports)]
use std::collections::BTreeMap;

#[derive(Parser)]
#[command(name = "evmdec", version, about = "EVM bytecode decompiler and security analyzer")]
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
            let code_end = info.metadata.as_ref().map(|m| m.offset).unwrap_or(prog.code.len());
            let rec = evmdec::cfg::recover(&prog, code_end);
            let total_nodes: usize = rec.main.nodes.len() + rec.functions.values().map(|u| u.nodes.len()).sum::<usize>() + rec.orphans.values().map(|u| u.nodes.len()).sum::<usize>();
            let code_blocks = prog.blocks.iter().filter(|b| b.start < code_end).count();
            println!("blocks={} code_blocks={} main_nodes={} functions={} orphans={} total_nodes={} unresolved_jumps={} budget_exhausted={} time={:?}",
                prog.blocks.len(), code_blocks, rec.main.nodes.len(), rec.functions.len(), rec.orphans.len(), total_nodes, rec.unresolved_jumps.len(), rec.budget_exhausted, t.elapsed());
            for pc in &rec.unresolved_jumps { println!("  unresolved jump ending at {:#x}", pc); }
            if let Ok(v) = std::env::var("EVMDEC_SUMMARY") {
                let an = evmdec::cfg::Analysis::new(&prog);
                for pcs in v.split(',') {
                    let pc = usize::from_str_radix(pcs.trim_start_matches("0x"), 16)?;
                    let b = prog.block_at_pc[&pc];
                    let s = an.summary(b);
                    println!("  summary {:#x}: exits={:?} may_halt={} unresolved={} blocks={}", pc, s.exits, s.may_halt, s.unresolved, s.blocks.len());
                }
            }
            if std::env::var("EVMDEC_CTX").is_ok() {
                let mut per: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
                for n in &rec.main.nodes { per.entry(n.block).or_default().push(n.id); }
                let mut v: Vec<(usize, usize)> = per.iter().map(|(b, v)| (v.len(), *b)).collect();
                v.sort_unstable_by(|a, b| b.cmp(a));
                for (cnt, b) in v.iter().take(5) {
                    println!("  main block {:#x} nodes={}", prog.blocks[*b].start, cnt);
                    for id in per[b].iter().take(5) {
                        let n = &rec.main.nodes[*id];
                        println!("     {:?} preds={:?}", n.entry, n.preds.iter().map(|p| format!("{:#x}", prog.blocks[rec.main.nodes[*p].block].start)).collect::<Vec<_>>());
                    }
                }
            }
            if std::env::var("EVMDEC_DEBUG").is_ok() {
                for (f, u) in &rec.functions {
                    let calls = u.nodes.iter().filter(|n| n.call.is_some()).count();
                    let rets: Vec<String> = u.nodes.iter().filter_map(|n| n.returns_via.map(|v| format!("{:?}", v))).collect();
                    println!("  function {:#x}: nodes={} calls={} returns_via={:?}", prog.blocks[*f].start, u.nodes.len(), calls, rets.iter().take(3).collect::<Vec<_>>());
                }
                for (b, u) in &rec.orphans {
                    println!("  orphan {:#x}: nodes={}", prog.blocks[*b].start, u.nodes.len());
                }
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
