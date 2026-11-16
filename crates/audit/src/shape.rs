use crate::trace::{Tag, DATA, DATA_WORDS};
use evmdec::abi::{self, Ty};
use evmdec::U256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Holds {
    Address,
    // An address the contract goes on to call.
    Callee,
    Flag,
    Small,
    Amount,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Word(Holds, U256),
    /* A byte string: the length it states, loose bytes at its start, then words laid out
    as a record of their own. The stated length may be less than what follows it. */
    Bytes {
        len: usize,
        lead: Vec<u8>,
        body: Vec<Node>,
    },
    List(Vec<Node>),
    Record(Vec<Node>),
}

// The call data as a tree. The bytes sent are always worked out from it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Shape {
    pub lead: Vec<u8>,
    pub args: Vec<Node>,
    // Loose bytes after everything else.
    pub spare: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    // Points at where a child starts. Worked out, never set.
    Head,
    Length,
    Value,
    Spare,
}

// What one word of the encoded call data is, and which node it belongs to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spot {
    pub at: usize,
    pub path: Vec<usize>,
    pub role: Role,
}

// The bytes a shape comes to, and what each word of them is.
pub struct Laid {
    pub data: Vec<u8>,
    pub spots: Vec<Spot>,
}

impl Laid {
    #[must_use]
    pub fn held(&self, spot: &Spot) -> U256 {
        let end = self.data.len().min(spot.at + 32);
        let mut word = [0u8; 32];
        word[..end - spot.at].copy_from_slice(&self.data[spot.at..end]);
        U256::from_be_bytes(&word)
    }

    #[must_use]
    pub fn spot_at(&self, word: usize) -> Option<&Spot> {
        let within = 4 + 32 * word..36 + 32 * word;
        self.spots.iter().find(|s| within.contains(&s.at))
    }

    // Every part of the call data a word was worked out from.
    #[must_use]
    pub fn behind(&self, tag: Tag) -> Vec<&Spot> {
        let words = (0..DATA_WORDS).filter(|w| tag.has(DATA) && tag.words >> w & 1 == 1);
        let spots = words.filter_map(|w| self.spot_at(w));
        spots.filter(|s| s.role != Role::Head).collect()
    }

    /* The part of the call data a word came from. A word reached through an offset
    carries the offset's place too, and an offset is never what a test is about. */
    #[must_use]
    pub fn about(&self, tag: Tag, seen: U256) -> Option<&Spot> {
        let found = self.behind(tag);
        let exact = found.iter().find(|s| self.held(s) == seen).copied();
        // A word that starts off the grid lies across two words of the call data.
        let single = found.len() == 1 || found.first().is_some_and(|s| s.at % 32 != 4);
        exact.or(found.first().copied().filter(|_| single))
    }
}

const MAX_NODES: usize = 256;
const MAX_ITEMS: usize = 8;
const MAX_BYTES: usize = 2_048;

#[must_use]
pub fn kind_of(ty: &str) -> Holds {
    let bits = |t: &str| {
        t.trim_start_matches("uint")
            .trim_start_matches("int")
            .parse::<u32>()
    };
    match ty {
        t if t.starts_with("address") => Holds::Address,
        "bool" => Holds::Flag,
        "bytes" | "string" => Holds::Other,
        t if t.starts_with("uint") || t.starts_with("int") => match bits(t) {
            Ok(n) if n < 64 => Holds::Small,
            _ => Holds::Amount,
        },
        _ => Holds::Amount,
    }
}

fn blank() -> Node {
    Node::Word(Holds::Other, U256::ZERO)
}

fn build(ty: &Ty, leaves: &mut dyn Iterator<Item = Holds>, room: &mut usize) -> Node {
    *room = room.saturating_sub(1);
    let repeated =
        |inner: &Ty, n: usize, leaves: &mut dyn Iterator<Item = Holds>, room: &mut usize| {
            let item = build(inner, leaves, room);
            let fits = n.min(*room / item.size().max(1)).max(1);
            *room = room.saturating_sub(fits * item.size());
            vec![item; fits]
        };
    match ty {
        _ if *room == 0 => blank(),
        Ty::Word => Node::Word(leaves.next().unwrap_or(Holds::Other), U256::ZERO),
        Ty::Bytes => {
            leaves.next();
            // Two fits a byte string and also a list that was recovered as one.
            Node::Bytes {
                len: 2,
                lead: Vec::new(),
                body: vec![blank(), blank()],
            }
        }
        Ty::Array(inner) => Node::List(repeated(inner, 1, leaves, room)),
        Ty::Fixed(inner, n) => Node::Record(repeated(inner, *n, leaves, room)),
        Ty::Tuple(parts) => Node::Record(parts.iter().map(|p| build(p, leaves, room)).collect()),
    }
}

impl Node {
    fn dynamic(&self) -> bool {
        match self {
            Node::Word(..) => false,
            Node::Bytes { .. } | Node::List(_) => true,
            Node::Record(parts) => parts.iter().any(Node::dynamic),
        }
    }

    fn children(&self) -> &[Node] {
        match self {
            Node::Word(..) => &[],
            Node::Bytes { body: items, .. } | Node::List(items) | Node::Record(items) => items,
        }
    }

    fn children_mut(&mut self) -> Option<&mut Vec<Node>> {
        match self {
            Node::Word(..) => None,
            Node::Bytes { body: items, .. } | Node::List(items) | Node::Record(items) => {
                Some(items)
            }
        }
    }

    fn size(&self) -> usize {
        1 + self.children().iter().map(Node::size).sum::<usize>()
    }

    fn each_word(&mut self, f: &mut dyn FnMut(&mut Holds, &mut U256)) {
        match self {
            Node::Word(kind, value) => f(kind, value),
            other => {
                for child in other.children_mut().into_iter().flatten() {
                    child.each_word(f);
                }
            }
        }
    }
}

struct Encoder {
    out: Vec<u8>,
    spots: Vec<Spot>,
    path: Vec<usize>,
}

impl Encoder {
    fn word(&mut self, value: U256, role: Role) {
        self.spots.push(Spot {
            at: self.out.len(),
            path: self.path.clone(),
            role,
        });
        self.out.extend_from_slice(&value.to_be_bytes());
    }

    fn sequence(&mut self, items: &[Node]) {
        let base = self.out.len();
        let mut heads = Vec::new();
        for (i, item) in items.iter().enumerate() {
            self.path.push(i);
            match item {
                _ if item.dynamic() => {
                    heads.push((i, self.out.len()));
                    self.word(U256::ZERO, Role::Head);
                }
                Node::Word(_, value) => self.word(*value, Role::Value),
                fixed => self.sequence(fixed.children()),
            }
            self.path.pop();
        }
        for (i, at) in heads {
            let offset = U256::from(self.out.len() - base);
            self.out[at..at + 32].copy_from_slice(&offset.to_be_bytes());
            self.path.push(i);
            match &items[i] {
                Node::Bytes { len, lead, body } => {
                    self.word(U256::from(*len), Role::Length);
                    let start = self.out.len();
                    self.out.extend_from_slice(lead);
                    self.sequence(body);
                    let whole = (self.out.len() - start).div_ceil(32) * 32;
                    self.out.resize(start + whole, 0);
                }
                Node::List(items) => {
                    self.word(U256::from(items.len()), Role::Length);
                    self.sequence(items);
                }
                other => self.sequence(other.children()),
            }
            self.path.pop();
        }
    }
}

impl Shape {
    #[must_use]
    pub fn of(selector: Option<u32>, types: &[String]) -> Shape {
        let mut room = MAX_NODES;
        let args = types.iter().map(|ty| {
            let names = ty.split(',').map(|leaf| {
                let name = leaf.replace(['(', ')', ' '], "");
                kind_of(name.split('[').next().unwrap_or(""))
            });
            build(&abi::parse(ty), &mut names.into_iter(), &mut room)
        });
        Shape {
            lead: selector.map_or(Vec::new(), |s| s.to_be_bytes().to_vec()),
            args: args.collect(),
            spare: Vec::new(),
        }
    }

    #[must_use]
    pub fn raw(data: &[u8]) -> Shape {
        Shape {
            lead: data.to_vec(),
            ..Shape::default()
        }
    }

    #[must_use]
    pub fn layout(&self) -> Laid {
        let mut enc = Encoder {
            out: self.lead.clone(),
            spots: Vec::new(),
            path: Vec::new(),
        };
        enc.sequence(&self.args);
        for chunk in 0..self.spare.len().div_ceil(32) {
            enc.spots.push(Spot {
                at: enc.out.len() + 32 * chunk,
                path: Vec::new(),
                role: Role::Spare,
            });
        }
        enc.out.extend_from_slice(&self.spare);
        Laid {
            data: enc.out,
            spots: enc.spots,
        }
    }

    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        self.layout().data
    }

    pub fn node_mut(&mut self, path: &[usize]) -> Option<&mut Node> {
        let (first, rest) = path.split_first()?;
        let mut node = self.args.get_mut(*first)?;
        for index in rest {
            node = node.children_mut()?.get_mut(*index)?;
        }
        Some(node)
    }

    pub fn each_word(&mut self, f: &mut dyn FnMut(&mut Holds, &mut U256)) {
        for arg in &mut self.args {
            arg.each_word(f);
        }
    }

    #[must_use]
    pub fn kinds(&self) -> Vec<Holds> {
        let mut kinds = Vec::new();
        self.clone().each_word(&mut |kind, _| kinds.push(*kind));
        kinds
    }

    pub fn put(&mut self, nth: usize, value: U256) -> bool {
        let mut at = 0;
        self.each_word(&mut |_, held| {
            if at == nth {
                *held = value;
            }
            at += 1;
        });
        nth < at
    }

    pub fn put_bytes(&mut self, path: &[usize], bytes: &[u8]) -> bool {
        let Some(node @ (Node::Bytes { .. } | Node::List(_))) = self.node_mut(path) else {
            return false;
        };
        *node = Node::Bytes {
            len: bytes.len(),
            lead: bytes.to_vec(),
            body: Vec::new(),
        };
        true
    }

    pub fn set(&mut self, spot: &Spot, value: U256) -> bool {
        match spot.role {
            Role::Head => false,
            Role::Length => value.as_usize().is_some_and(|n| self.resize(&spot.path, n)),
            Role::Value => match self.node_mut(&spot.path) {
                Some(Node::Word(_, held)) => {
                    *held = value;
                    true
                }
                _ => false,
            },
            Role::Spare => {
                let start = self.encode().len() - self.spare.len();
                let at = spot.at.saturating_sub(start);
                if self.spare.len() < at + 32 {
                    self.spare.resize(at + 32, 0);
                }
                self.spare[at..at + 32].copy_from_slice(&value.to_be_bytes());
                true
            }
        }
    }

    /* A list gets the items it lacks, each a copy of its first. A byte string gets the
    words that hold the length it now states. */
    pub fn resize(&mut self, path: &[usize], n: usize) -> bool {
        match self.node_mut(path) {
            Some(Node::List(items)) if n <= MAX_ITEMS => {
                let first = items.first().cloned().unwrap_or_else(blank);
                items.resize(n, first);
                true
            }
            Some(Node::Bytes { len, lead, body }) if n <= MAX_BYTES => {
                *len = n;
                let mut enc = Encoder {
                    out: lead.clone(),
                    spots: Vec::new(),
                    path: Vec::new(),
                };
                enc.sequence(body);
                let lacks = n.saturating_sub(enc.out.len()).div_ceil(32);
                body.extend(std::iter::repeat_with(blank).take(lacks));
                true
            }
            _ => false,
        }
    }

    // How many lists have nothing in them.
    #[must_use]
    pub fn hollow(&self) -> usize {
        fn count(node: &Node) -> usize {
            let own = usize::from(matches!(node, Node::List(items) if items.is_empty()));
            own + node.children().iter().map(count).sum::<usize>()
        }
        self.args.iter().map(count).sum()
    }

    // The shape with nothing in its words: what is laid out where, and no more.
    #[must_use]
    pub fn frame(&self) -> Shape {
        let mut bare = self.clone();
        bare.each_word(&mut |holds, held| (*holds, *held) = (Holds::Other, U256::ZERO));
        bare
    }

    // Every list with two items, where it had one.
    #[must_use]
    pub fn paired(&self) -> Option<Shape> {
        fn pair(node: &mut Node) -> bool {
            let mut any = false;
            if let Node::List(items) = node {
                if let [first] = &items[..] {
                    items.push(first.clone());
                    any = true;
                }
            }
            for child in node.children_mut().into_iter().flatten() {
                any |= pair(child);
            }
            any
        }
        let mut next = self.clone();
        let mut any = false;
        for arg in &mut next.args {
            any |= pair(arg);
        }
        any.then_some(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(types: &[&str]) -> Shape {
        let types: Vec<String> = types.iter().map(|t| (*t).to_string()).collect();
        Shape::of(Some(1), &types)
    }

    fn words(data: &[u8]) -> Vec<u64> {
        data[4..]
            .chunks(32)
            .map(|w| U256::from_be_bytes(w).low_u64())
            .collect()
    }

    #[test]
    fn a_shape_from_types_is_laid_out_as_the_types_are() {
        for types in [
            vec!["address", "uint256"],
            vec!["uint256", "bytes"],
            vec!["(address,bytes)[]"],
            vec!["address[]", "uint256"],
            vec![
                "(uint256,(bool,bytes)[2],uint8[3])",
                "string",
                "uint256[][]",
            ],
        ] {
            let owned: Vec<String> = types.iter().map(|t| (*t).to_string()).collect();
            let known = abi::layout(Some(1), &owned);
            let laid = shape(&types).layout();
            assert_eq!(laid.data, known.calldata, "{types:?}");
            let heads = laid.spots.iter().filter(|s| s.role == Role::Head);
            let mut heads: Vec<usize> = heads.map(|s| (s.at - 4) / 32).collect();
            heads.sort_unstable();
            let mut fixed = known.fixed.clone();
            fixed.sort_unstable();
            assert_eq!(heads, fixed, "{types:?}");
        }
    }

    #[test]
    fn words_inside_records_and_lists_keep_their_kinds() {
        let s = shape(&["(address,uint256,bool)[]", "(uint8,bytes,address)"]);
        use Holds::{Address, Amount, Flag, Other, Small};
        assert_eq!(
            s.kinds(),
            [Address, Amount, Flag, Small, Other, Other, Address]
        );
    }

    #[test]
    fn a_grown_byte_string_keeps_every_offset_right() {
        let mut s = shape(&["bytes", "uint256[]"]);
        let spots = s.layout().spots;
        let length = spots.iter().find(|s| s.role == Role::Length).expect("one");
        assert!(s.set(length, U256::from_u64(0x60)));
        assert_eq!(words(&s.encode()), [0x40, 0xc0, 0x60, 0, 0, 0, 1, 0]);
        let spots = s.layout().spots;
        let third = spots.iter().find(|s| s.at == 4 + 32 * 5).expect("a word");
        assert!(s.set(third, U256::from_u64(7)));
        let list = spots.iter().rfind(|s| s.role == Role::Length).expect("two");
        assert!(s.set(list, U256::from_u64(3)));
        assert_eq!(words(&s.encode()), [0x40, 0xc0, 0x60, 0, 0, 7, 3, 0, 0, 0]);
        assert_eq!(s.hollow(), 0);
        assert!(s.set(list, U256::ZERO));
        assert_eq!(s.hollow(), 1);
    }

    #[test]
    fn loose_bytes_at_the_start_of_a_byte_string_shift_its_words() {
        let mut s = shape(&["bytes"]);
        let Some(Node::Bytes { len, lead, body }) = s.node_mut(&[0]) else {
            panic!("a byte string");
        };
        (*len, *lead) = (36, vec![0xaa, 0xbb, 0xcc, 0xdd]);
        body.truncate(1);
        let Laid { data, spots } = s.layout();
        assert_eq!(data.len(), 4 + 32 * 4);
        assert_eq!(&data[68..72], [0xaa, 0xbb, 0xcc, 0xdd]);
        assert_eq!(
            spots.last().map(|s| (s.at, s.role)),
            Some((72, Role::Value))
        );
    }

    #[test]
    fn a_type_nested_without_end_gets_a_bounded_shape() {
        let nested = format!("uint256{}", "[4]".repeat(40));
        let s = Shape::of(Some(1), &[nested]);
        assert!(s.kinds().len() <= MAX_NODES);
    }
}
