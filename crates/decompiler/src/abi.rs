use crate::u256::U256;

pub const SEL_TRANSFER: u32 = 0xa905_9cbb;
pub const SEL_TRANSFER_FROM: u32 = 0x23b8_72dd;
pub const SEL_OWNER_OF: u32 = 0x6352_211e;
pub const SEL_BALANCE_OF: u32 = 0x70a0_8231;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Word,
    Bytes,
    Array(Box<Ty>),
    Fixed(Box<Ty>, usize),
    Tuple(Vec<Ty>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub calldata: Vec<u8>,
    pub fixed: Vec<usize>,
}

fn split_top(list: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let (mut depth, mut start) = (0usize, 0usize);
    for (i, c) in list.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(&list[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < list.len() {
        parts.push(&list[start..]);
    }
    parts
}

// A type text comes from a signature list anyone can add to.
// These two bounds keep a nested type from costing more than a small layout.
const MAX_TYPE_TEXT: usize = 512;
const MAX_WORDS: usize = 1024;

pub fn parse(ty: &str) -> Ty {
    let ty = ty.trim();
    if ty.len() > MAX_TYPE_TEXT {
        return Ty::Word;
    }
    if let Some(open) = ty.rfind('[') {
        if ty.ends_with(']') && !ty[open..].contains(')') {
            let inner = Box::new(parse(&ty[..open]));
            return match ty[open + 1..ty.len() - 1].parse::<usize>() {
                Ok(n) => Ty::Fixed(inner, n.min(4)),
                Err(_) => Ty::Array(inner),
            };
        }
    }
    if let Some(inner) = ty.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        return Ty::Tuple(split_top(inner).into_iter().map(parse).collect());
    }
    match ty {
        "bytes" | "string" => Ty::Bytes,
        _ => Ty::Word,
    }
}

fn dynamic(ty: &Ty) -> bool {
    match ty {
        Ty::Word => false,
        Ty::Bytes | Ty::Array(_) => true,
        Ty::Fixed(inner, _) => dynamic(inner),
        Ty::Tuple(parts) => parts.iter().any(dynamic),
    }
}

fn head_words(ty: &Ty) -> usize {
    match ty {
        _ if dynamic(ty) => 1,
        Ty::Fixed(inner, n) => n.saturating_mul(head_words(inner)),
        Ty::Tuple(parts) => parts
            .iter()
            .fold(0usize, |sum, part| sum.saturating_add(head_words(part))),
        _ => 1,
    }
}

struct Encoder {
    words: Vec<U256>,
    fixed: Vec<usize>,
    elements: usize,
}

impl Encoder {
    fn sequence(&mut self, items: &[Ty]) {
        let base = self.words.len();
        let head = items
            .iter()
            .fold(0usize, |sum, item| sum.saturating_add(head_words(item)));
        if base.saturating_add(head) > MAX_WORDS {
            return;
        }
        self.words.resize(base + head, U256::ZERO);
        let mut at = base;
        for item in items {
            if dynamic(item) {
                let offset = (self.words.len() - base) * 32;
                self.words[at] = U256::from(offset);
                self.fixed.push(at);
                self.tail(item);
                at += 1;
            } else {
                at += head_words(item);
            }
        }
    }

    fn tail(&mut self, ty: &Ty) {
        match ty {
            Ty::Bytes => {
                // Two fits a byte string and also an array that was recovered as one.
                self.words.push(U256::from_u64(2));
                self.words.push(U256::ZERO);
                self.words.push(U256::ZERO);
            }
            Ty::Array(inner) => {
                self.words.push(U256::from(self.elements));
                self.sequence(&vec![(**inner).clone(); self.elements]);
            }
            Ty::Fixed(inner, n) => self.sequence(&vec![(**inner).clone(); *n]),
            Ty::Tuple(parts) => self.sequence(parts),
            Ty::Word => self.words.push(U256::ZERO),
        }
    }
}

pub fn layout(selector: Option<u32>, types: &[String]) -> Layout {
    layout_with(selector, types, 1)
}

// Only offsets are fixed. A length stays free because a function may bound it,
// and a recovered byte string may really be an array.
pub fn layout_with(selector: Option<u32>, types: &[String], elements: usize) -> Layout {
    let items: Vec<Ty> = types.iter().map(|t| parse(t)).collect();
    let mut enc = Encoder {
        words: Vec::new(),
        fixed: Vec::new(),
        elements,
    };
    enc.sequence(&items);
    let mut calldata = Vec::with_capacity(4 + 32 * enc.words.len());
    if let Some(selector) = selector {
        calldata.extend_from_slice(&selector.to_be_bytes());
    }
    for w in &enc.words {
        calldata.extend_from_slice(&w.to_be_bytes());
    }
    Layout {
        calldata,
        fixed: enc.fixed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(layout: &Layout) -> Vec<u64> {
        layout.calldata[4..]
            .chunks(32)
            .map(|w| U256::from_be_bytes(w).low_u64())
            .collect()
    }

    #[test]
    fn static_words_take_one_slot_each() {
        let l = layout(Some(1), &["address".into(), "uint256".into()]);
        assert_eq!(words(&l), [0, 0]);
        assert!(l.fixed.is_empty());
    }

    #[test]
    fn a_byte_string_gets_an_offset_a_length_and_two_words() {
        let l = layout(Some(1), &["uint256".into(), "bytes".into()]);
        assert_eq!(words(&l), [0, 0x40, 2, 0, 0]);
        assert_eq!(l.fixed, [1]);
    }

    #[test]
    fn an_array_of_tuples_with_bytes_nests_its_offsets() {
        let l = layout(Some(1), &["(address,bytes)[]".into()]);
        assert_eq!(words(&l), [0x20, 1, 0x20, 0, 0x40, 2, 0, 0]);
        assert_eq!(l.fixed, [0, 2, 4]);
    }

    #[test]
    fn a_deeply_nested_type_gets_a_bounded_layout() {
        let nested = format!("uint256{}", "[4]".repeat(40));
        assert!(layout(Some(1), &[nested]).calldata.len() <= 4 + 32 * MAX_WORDS);
        let dynamic = format!("bytes{}", "[4]".repeat(40));
        assert!(layout(Some(1), &[dynamic]).calldata.len() < 64 * MAX_WORDS);
    }

    #[test]
    fn an_array_can_be_given_two_elements() {
        let l = layout_with(Some(1), &["address[]".into(), "uint256".into()], 2);
        assert_eq!(words(&l), [0x40, 0, 2, 0, 0]);
        assert_eq!(l.fixed, [0]);
    }
}
