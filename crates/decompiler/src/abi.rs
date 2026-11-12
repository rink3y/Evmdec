use crate::u256::U256;

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

pub fn parse(ty: &str) -> Ty {
    let ty = ty.trim();
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
        Ty::Fixed(inner, n) => n * head_words(inner),
        Ty::Tuple(parts) => parts.iter().map(head_words).sum(),
        _ => 1,
    }
}

struct Encoder {
    words: Vec<U256>,
    fixed: Vec<usize>,
}

impl Encoder {
    fn sequence(&mut self, items: &[Ty]) {
        let base = self.words.len();
        let head: usize = items.iter().map(head_words).sum();
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
                self.fixed.push(self.words.len());
                self.words.push(U256::from_u64(32));
                self.words.push(U256::ZERO);
            }
            Ty::Array(inner) => {
                self.fixed.push(self.words.len());
                self.words.push(U256::ONE);
                self.sequence(std::slice::from_ref(inner));
            }
            Ty::Fixed(inner, n) => self.sequence(&vec![(**inner).clone(); *n]),
            Ty::Tuple(parts) => self.sequence(parts),
            Ty::Word => self.words.push(U256::ZERO),
        }
    }
}

// Every array gets one element and every byte string one word.
// The offsets and lengths that make this layout valid are listed as fixed.
pub fn layout(selector: Option<u32>, types: &[String]) -> Layout {
    let items: Vec<Ty> = types.iter().map(|t| parse(t)).collect();
    let mut enc = Encoder {
        words: Vec::new(),
        fixed: Vec::new(),
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
    fn a_byte_string_gets_an_offset_a_length_and_one_word() {
        let l = layout(Some(1), &["uint256".into(), "bytes".into()]);
        assert_eq!(words(&l), [0, 0x40, 32, 0]);
        assert_eq!(l.fixed, [1, 2]);
    }

    #[test]
    fn an_array_of_tuples_with_bytes_nests_its_offsets() {
        let l = layout(Some(1), &["(address,bytes)[]".into()]);
        assert_eq!(words(&l), [0x20, 1, 0x20, 0, 0x40, 32, 0]);
        assert_eq!(l.fixed, [0, 1, 2, 4, 5]);
    }
}
