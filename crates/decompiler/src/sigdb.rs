//! A local copy of the full signature database (Sourcify's 4byte export, ~10.7 million
//! entries) as one sorted index file searched in place.
//!
//! The file is never loaded: a lookup is a binary search over fixed-width entries read with
//! positional reads, so a process pays nothing at start-up and the operating system's page cache
//! keeps the hot part of the file in memory. Format (`EVMSIG1`, little-endian):
//!
//! ```text
//! 0..8    magic "EVMSIG1\n"
//! 8..16   u64 entry count n
//! 16..24  u64 absolute offset of the string pool
//! 24..    n entries of 12 bytes: u64 prefix (first 8 bytes of the keccak256 hash, big-endian),
//!         u32 offset of the signature inside the pool; sorted by (prefix, offset)
//! pool    NUL-terminated signatures
//! ```
//!
//! A 4-byte selector selects the entries whose prefix starts with it; a 32-byte topic selects
//! the entries with the same 8-byte prefix and the candidate is confirmed by hashing it.
//! `corpus/build_sigs.py` builds the file from the Parquet export; [`write()`] builds one from
//! memory (tests, small custom dictionaries).

use crate::keccak;
use std::collections::HashSet;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

const MAGIC: &[u8; 8] = b"EVMSIG1\n";
const HEADER_LEN: u64 = 24;
const ENTRY_LEN: u64 = 12;
/// Longest signature the reader accepts (the export's longest is about 1,200 bytes).
const MAX_SIG: usize = 8192;
/// Most entries one selector or prefix may map to; more than this is a corrupt file.
const MAX_FANOUT: usize = 256;

/// An open index file.
///
/// The index is advisory: a read error during a lookup (a truncated or corrupt file) is reported
/// as "no signature", never as a failure of the decompilation that asked.
#[derive(Debug)]
pub struct SigDb {
    file: File,
    entries: u64,
    pool: u64,
    len: u64,
}

/// Which part of the stored hash prefix a lookup compares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Match {
    /// The top 4 bytes: a function or error selector.
    Selector,
    /// All 8 bytes: an event topic, to be confirmed by hashing the candidate.
    Prefix,
}

#[cfg(unix)]
fn read_at(file: &File, off: u64, buf: &mut [u8]) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    file.read_exact_at(buf, off)
}

#[cfg(windows)]
fn read_at(file: &File, off: u64, buf: &mut [u8]) -> io::Result<()> {
    use std::os::windows::fs::FileExt;
    let mut done = 0;
    while done < buf.len() {
        let n = file.seek_read(&mut buf[done..], off + done as u64)?;
        if n == 0 {
            return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "short read"));
        }
        done += n;
    }
    Ok(())
}

#[cfg(not(any(unix, windows)))]
fn read_at(file: &File, off: u64, buf: &mut [u8]) -> io::Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    let mut f = file.try_clone()?;
    f.seek(SeekFrom::Start(off))?;
    f.read_exact(buf)
}

impl SigDb {
    /// Open an index file, checking its header.
    ///
    /// # Errors
    /// The file cannot be read, or it is not an `EVMSIG1` index.
    pub fn open(path: &Path) -> io::Result<SigDb> {
        let file = File::open(path)?;
        let mut header = [0u8; HEADER_LEN as usize];
        read_at(&file, 0, &mut header)?;
        if &header[0..8] != MAGIC {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "not an EVMSIG1 signature index",
            ));
        }
        let entries =
            u64::from_le_bytes(header[8..16].try_into().expect("header[8..16] is 8 bytes"));
        let pool = u64::from_le_bytes(
            header[16..24]
                .try_into()
                .expect("header[16..24] is 8 bytes"),
        );
        let len = file.metadata()?.len();
        if pool != HEADER_LEN + entries * ENTRY_LEN || len < pool {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "signature index header does not match its size",
            ));
        }
        Ok(SigDb {
            file,
            entries,
            pool,
            len,
        })
    }

    /// Number of signatures in the index.
    #[must_use]
    pub fn len(&self) -> usize {
        usize::try_from(self.entries)
            .expect("a file with more than usize::MAX entries cannot be read")
    }

    /// Whether the index holds no signatures.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries == 0
    }

    fn entry(&self, i: u64) -> io::Result<(u64, u32)> {
        let mut buf = [0u8; ENTRY_LEN as usize];
        read_at(&self.file, HEADER_LEN + i * ENTRY_LEN, &mut buf)?;
        Ok((
            u64::from_le_bytes(buf[0..8].try_into().expect("buf[0..8] is 8 bytes")),
            u32::from_le_bytes(buf[8..12].try_into().expect("buf[8..12] is 4 bytes")),
        ))
    }

    /// First entry whose prefix is at least `prefix`.
    fn lower_bound(&self, prefix: u64) -> io::Result<u64> {
        let (mut lo, mut hi) = (0u64, self.entries);
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.entry(mid)?.0 < prefix {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        Ok(lo)
    }

    fn string_at(&self, off: u32) -> io::Result<String> {
        let mut out: Vec<u8> = Vec::new();
        let mut pos = self.pool + off as u64;
        let end = self.len;
        let mut chunk = [0u8; 96];
        while out.len() < MAX_SIG && pos < end {
            let n = chunk.len().min((end - pos) as usize);
            read_at(&self.file, pos, &mut chunk[..n])?;
            if let Some(nul) = chunk[..n].iter().position(|b| *b == 0) {
                out.extend_from_slice(&chunk[..nul]);
                return String::from_utf8(out)
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e));
            }
            out.extend_from_slice(&chunk[..n]);
            pos += n as u64;
        }
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unterminated signature in index",
        ))
    }

    /// Up to `limit` signatures stored under `prefix` (an 8-byte hash prefix) or, with
    /// `Match::Selector`, under its top 4 bytes, in file order.
    fn candidates(&self, prefix: u64, what: Match, limit: usize) -> io::Result<Vec<String>> {
        let mut out = Vec::new();
        let mut i = self.lower_bound(match what {
            Match::Selector => prefix & 0xffff_ffff_0000_0000,
            Match::Prefix => prefix,
        })?;
        let same = |p: u64| match what {
            Match::Selector => p >> 32 == prefix >> 32,
            Match::Prefix => p == prefix,
        };
        while i < self.entries && out.len() < limit {
            let (p, off) = self.entry(i)?;
            if !same(p) {
                break;
            }
            out.push(self.string_at(off)?);
            i += 1;
        }
        Ok(out)
    }

    /// Function or error signatures for a 4-byte selector, shortest first (the canonical name
    /// of a collision is almost always the shorter one). The index stores no kind, so a
    /// selector that is both a function and a custom error returns both. Empty on a read error.
    #[must_use]
    pub fn selector(&self, selector: u32) -> Vec<String> {
        let mut v = self
            .candidates((selector as u64) << 32, Match::Selector, MAX_FANOUT)
            .unwrap_or_default();
        v.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
        v.dedup();
        v
    }

    /// The event signature whose keccak256 is `topic`, if the index holds one. `None` on a read
    /// error.
    #[must_use]
    pub fn topic(&self, topic: &[u8; 32]) -> Option<String> {
        let prefix = u64::from_be_bytes(topic[0..8].try_into().expect("topic[0..8] is 8 bytes"));
        self.candidates(prefix, Match::Prefix, MAX_FANOUT)
            .unwrap_or_default()
            .into_iter()
            .find(|s| keccak::keccak256(s.as_bytes()) == *topic)
    }
}

/// Build an index file from `(keccak256 hash, signature)` pairs. Duplicate signatures are kept
/// once.
///
/// # Errors
/// The file cannot be written.
pub fn write(path: &Path, entries: impl IntoIterator<Item = ([u8; 32], String)>) -> io::Result<()> {
    let mut pool: Vec<u8> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    let mut table: Vec<(u64, u32)> = Vec::new();
    for (hash, sig) in entries {
        if seen.contains(&sig) {
            continue;
        }
        let off = u32::try_from(pool.len())
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "pool over 4 GiB"))?;
        pool.extend_from_slice(sig.as_bytes());
        pool.push(0);
        let prefix = u64::from_be_bytes(hash[0..8].try_into().expect("hash[0..8] is 8 bytes"));
        table.push((prefix, off));
        seen.insert(sig);
    }
    table.sort_unstable();
    let mut out = io::BufWriter::new(File::create(path)?);
    out.write_all(MAGIC)?;
    out.write_all(&(table.len() as u64).to_le_bytes())?;
    out.write_all(&(HEADER_LEN + table.len() as u64 * ENTRY_LEN).to_le_bytes())?;
    for (prefix, off) in &table {
        out.write_all(&prefix.to_le_bytes())?;
        out.write_all(&off.to_le_bytes())?;
    }
    out.write_all(&pool)?;
    out.flush()
}

/// Where the index is looked for when `EVMDEC_SIGS` is not set.
fn default_paths() -> Vec<PathBuf> {
    let mut v = vec![PathBuf::from("sigs.idx")];
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            v.push(dir.join("sigs.idx"));
        }
    }
    v.push(PathBuf::from("/var/lib/evmdec/sigs.idx"));
    if let Ok(home) = std::env::var("HOME") {
        v.push(PathBuf::from(home).join(".evmdec").join("sigs.idx"));
    }
    v
}

/// The process-wide index: `EVMDEC_SIGS` names the file (an empty value disables the lookup),
/// otherwise the first of `./sigs.idx`, `<binary dir>/sigs.idx`, `/var/lib/evmdec/sigs.idx`
/// and `~/.evmdec/sigs.idx` that opens. `None` when there is none.
#[must_use]
pub fn global() -> Option<&'static SigDb> {
    static DB: OnceLock<Option<SigDb>> = OnceLock::new();
    DB.get_or_init(|| {
        let paths: Vec<PathBuf> = match std::env::var("EVMDEC_SIGS") {
            Ok(p) if p.is_empty() => return None,
            Ok(p) => vec![PathBuf::from(p)],
            Err(_) => default_paths(),
        };
        paths.iter().find_map(|p| SigDb::open(p).ok())
    })
    .as_ref()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h(s: &str) -> [u8; 32] {
        keccak::keccak256(s.as_bytes())
    }

    /// A fresh directory under the system temp dir, removed when dropped (also on a failed
    /// assertion).
    struct TempDir(PathBuf);

    impl TempDir {
        fn new(tag: &str) -> TempDir {
            let dir = std::env::temp_dir().join(format!("evmdec-{tag}-{}", std::process::id()));
            std::fs::create_dir_all(&dir).unwrap();
            TempDir(dir)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn selector_and_topic_lookups_round_trip() {
        let dir = TempDir::new("sigdb");
        let path = dir.0.join("sigs.idx");
        let mut forged = h("transfer(address,uint256)");
        forged[4] ^= 0xff;
        write(
            &path,
            vec![
                (h("balanceOf(address)"), "balanceOf(address)".to_string()),
                (
                    h("transfer(address,uint256)"),
                    "transfer(address,uint256)".to_string(),
                ),
                (
                    forged,
                    "transfer_with_a_longer_colliding_name(address,uint256)".to_string(),
                ),
                (
                    h("Transfer(address,address,uint256)"),
                    "Transfer(address,address,uint256)".to_string(),
                ),
                (
                    h("Approval(address,address,uint256)"),
                    "Approval(address,address,uint256)".to_string(),
                ),
                (h("balanceOf(address)"), "balanceOf(address)".to_string()),
            ],
        )
        .unwrap();
        let db = SigDb::open(&path).unwrap();
        assert_eq!(db.len(), 5, "duplicates are stored once");
        assert_eq!(
            db.selector(0xa9059cbb),
            vec![
                "transfer(address,uint256)".to_string(),
                "transfer_with_a_longer_colliding_name(address,uint256)".to_string()
            ]
        );
        assert_eq!(
            db.selector(0x70a08231),
            vec!["balanceOf(address)".to_string()]
        );
        assert!(db.selector(0x12345678).is_empty());
        assert_eq!(
            db.topic(&h("Transfer(address,address,uint256)")).as_deref(),
            Some("Transfer(address,address,uint256)")
        );
        assert_eq!(db.topic(&h("Nothing()")), None);
    }

    #[test]
    fn open_rejects_other_files() {
        let dir = TempDir::new("sigdb-bad");
        let path = dir.0.join("not.idx");
        std::fs::write(&path, b"hello world, this is not an index at all").unwrap();
        assert!(SigDb::open(&path).is_err());
    }
}
