pub fn decode(s: &str) -> Result<Vec<u8>, String> {
    let s = s.trim();
    let s = s
        .strip_prefix("0x")
        .or_else(|| s.strip_prefix("0X"))
        .unwrap_or(s);
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    if !s.len().is_multiple_of(2) {
        return Err("hex string has odd length".into());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    let b = s.as_bytes();
    for i in (0..b.len()).step_by(2) {
        let hi = (b[i] as char)
            .to_digit(16)
            .ok_or_else(|| format!("invalid hex character {:?} at offset {}", b[i] as char, i))?;
        let lo = (b[i + 1] as char).to_digit(16).ok_or_else(|| {
            format!(
                "invalid hex character {:?} at offset {}",
                b[i + 1] as char,
                i + 1
            )
        })?;
        out.push((hi * 16 + lo) as u8);
    }
    Ok(out)
}

pub fn encode(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2 + 2);
    s.push_str("0x");
    for x in b {
        s.push_str(&format!("{:02x}", x));
    }
    s
}

pub fn encode_plain(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}
