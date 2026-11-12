const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
const ROTC: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];
const PILN: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

fn keccakf(st: &mut [u64; 25]) {
    for rc in RC {
        let mut bc = [0u64; 5];
        for i in 0..5 {
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        }
        for i in 0..5 {
            let t = bc[(i + 4) % 5] ^ bc[(i + 1) % 5].rotate_left(1);
            for j in (0..25).step_by(5) {
                st[j + i] ^= t;
            }
        }
        let mut t = st[1];
        for i in 0..24 {
            let j = PILN[i];
            let tmp = st[j];
            st[j] = t.rotate_left(ROTC[i]);
            t = tmp;
        }
        for j in (0..25).step_by(5) {
            let mut b = [0u64; 5];
            b.copy_from_slice(&st[j..j + 5]);
            for i in 0..5 {
                st[j + i] ^= (!b[(i + 1) % 5]) & b[(i + 2) % 5];
            }
        }
        st[0] ^= rc;
    }
}

pub fn keccak256(data: &[u8]) -> [u8; 32] {
    const RATE: usize = 136;
    let mut st = [0u64; 25];
    let mut block = [0u8; RATE];
    let (chunks, rem) = data.as_chunks::<RATE>();
    for chunk in chunks {
        absorb(&mut st, chunk);
    }
    block[..rem.len()].copy_from_slice(rem);
    block[rem.len()] ^= 0x01;
    block[RATE - 1] ^= 0x80;
    absorb(&mut st, &block);
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[i * 8..i * 8 + 8].copy_from_slice(&st[i].to_le_bytes());
    }
    out
}

fn absorb(st: &mut [u64; 25], block: &[u8]) {
    for i in 0..block.len() / 8 {
        let mut v = [0u8; 8];
        v.copy_from_slice(&block[i * 8..i * 8 + 8]);
        st[i] ^= u64::from_le_bytes(v);
    }
    keccakf(st);
}

pub fn selector(sig: &str) -> [u8; 4] {
    let h = keccak256(sig.as_bytes());
    [h[0], h[1], h[2], h[3]]
}

pub fn selector_u32(sig: &str) -> u32 {
    u32::from_be_bytes(selector(sig))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }
    #[test]
    fn known_vectors() {
        assert_eq!(
            hex(&keccak256(b"")),
            "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
        );
        assert_eq!(hex(&selector("transfer(address,uint256)")), "a9059cbb");
        assert_eq!(hex(&selector("balanceOf(address)")), "70a08231");
        assert_eq!(
            hex(&keccak256(b"Transfer(address,address,uint256)")),
            "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef"
        );
        let long = vec![0x61u8; 300];
        assert_eq!(hex(&keccak256(&long)).len(), 64);
        assert_eq!(
            hex(&keccak256(b"eip1967.proxy.implementation")),
            "360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbd"
        );
    }
}
