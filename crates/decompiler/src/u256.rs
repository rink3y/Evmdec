use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct U256(pub [u64; 4]);

impl U256 {
    pub const ZERO: U256 = U256([0, 0, 0, 0]);
    pub const ONE: U256 = U256([1, 0, 0, 0]);
    pub const MAX: U256 = U256([u64::MAX; 4]);

    pub const fn from_u64(v: u64) -> U256 {
        U256([v, 0, 0, 0])
    }
    pub const fn from_u128(v: u128) -> U256 {
        U256([v as u64, (v >> 64) as u64, 0, 0])
    }

    pub fn from_be_bytes(bytes: &[u8]) -> U256 {
        let mut buf = [0u8; 32];
        let n = bytes.len().min(32);
        buf[32 - n..].copy_from_slice(&bytes[bytes.len() - n..]);
        let mut limbs = [0u64; 4];
        for i in 0..4 {
            let mut v = 0u64;
            for j in 0..8 {
                v = (v << 8) | buf[(3 - i) * 8 + j] as u64;
            }
            limbs[i] = v;
        }
        U256(limbs)
    }

    pub fn to_be_bytes(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for i in 0..4 {
            let v = self.0[i];
            for j in 0..8 {
                out[(3 - i) * 8 + j] = (v >> (56 - 8 * j)) as u8;
            }
        }
        out
    }

    pub fn is_zero(&self) -> bool {
        self.0 == [0, 0, 0, 0]
    }
    pub fn low_u64(&self) -> u64 {
        self.0[0]
    }
    pub fn low_u128(&self) -> u128 {
        self.0[0] as u128 | ((self.0[1] as u128) << 64)
    }
    pub fn fits_u64(&self) -> bool {
        self.0[1] == 0 && self.0[2] == 0 && self.0[3] == 0
    }
    pub fn as_usize(&self) -> Option<usize> {
        if self.fits_u64() && self.0[0] <= usize::MAX as u64 {
            Some(self.0[0] as usize)
        } else {
            None
        }
    }
    pub fn bits(&self) -> u32 {
        for i in (0..4).rev() {
            if self.0[i] != 0 {
                return 64 * i as u32 + (64 - self.0[i].leading_zeros());
            }
        }
        0
    }
    pub fn byte_len(&self) -> usize {
        self.bits().div_ceil(8) as usize
    }
    pub fn bit(&self, i: u32) -> bool {
        if i >= 256 {
            return false;
        }
        (self.0[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }
    pub fn leading_zeros(&self) -> u32 {
        256 - self.bits()
    }
    pub fn trailing_zeros(&self) -> u32 {
        for i in 0..4 {
            if self.0[i] != 0 {
                return 64 * i as u32 + self.0[i].trailing_zeros();
            }
        }
        256
    }
    pub fn count_ones(&self) -> u32 {
        self.0.iter().map(|l| l.count_ones()).sum()
    }
    pub fn is_power_of_two(&self) -> bool {
        self.count_ones() == 1
    }
    pub fn is_low_mask(&self) -> bool {
        !self.is_zero() && (*self + U256::ONE).is_power_of_two() || *self == U256::MAX
    }

    pub fn overflowing_add(self, rhs: U256) -> (U256, bool) {
        let mut r = [0u64; 4];
        let mut carry = 0u64;
        for (i, limb) in r.iter_mut().enumerate() {
            let (s1, c1) = self.0[i].overflowing_add(rhs.0[i]);
            let (s2, c2) = s1.overflowing_add(carry);
            *limb = s2;
            carry = (c1 as u64) + (c2 as u64);
        }
        (U256(r), carry != 0)
    }
    pub fn overflowing_sub(self, rhs: U256) -> (U256, bool) {
        let mut r = [0u64; 4];
        let mut borrow = 0u64;
        for (i, limb) in r.iter_mut().enumerate() {
            let (s1, b1) = self.0[i].overflowing_sub(rhs.0[i]);
            let (s2, b2) = s1.overflowing_sub(borrow);
            *limb = s2;
            borrow = (b1 as u64) + (b2 as u64);
        }
        (U256(r), borrow != 0)
    }
    pub fn wrapping_add(self, rhs: U256) -> U256 {
        self.overflowing_add(rhs).0
    }
    pub fn wrapping_sub(self, rhs: U256) -> U256 {
        self.overflowing_sub(rhs).0
    }
    pub fn wrapping_mul(self, rhs: U256) -> U256 {
        let mut r = [0u64; 8];
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                if i + j >= 8 {
                    break;
                }
                let t = r[i + j] as u128 + (self.0[i] as u128) * (rhs.0[j] as u128) + carry;
                r[i + j] = t as u64;
                carry = t >> 64;
            }
            let mut k = i + 4;
            while carry != 0 && k < 8 {
                let t = r[k] as u128 + carry;
                r[k] = t as u64;
                carry = t >> 64;
                k += 1;
            }
        }
        U256([r[0], r[1], r[2], r[3]])
    }
    pub fn full_mul(self, rhs: U256) -> (U256, U256) {
        let mut r = [0u64; 8];
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                let t = r[i + j] as u128 + (self.0[i] as u128) * (rhs.0[j] as u128) + carry;
                r[i + j] = t as u64;
                carry = t >> 64;
            }
            r[i + 4] = carry as u64;
        }
        (
            U256([r[0], r[1], r[2], r[3]]),
            U256([r[4], r[5], r[6], r[7]]),
        )
    }

    pub fn sar(self, n: u32) -> U256 {
        let neg = self.bit(255);
        if n >= 256 {
            return if neg { U256::MAX } else { U256::ZERO };
        }
        let r = self >> n;
        if neg && n > 0 {
            r | (U256::MAX << (256 - n))
        } else {
            r
        }
    }

    pub fn div_rem(self, rhs: U256) -> (U256, U256) {
        if rhs.is_zero() {
            return (U256::ZERO, U256::ZERO);
        }
        if self < rhs {
            return (U256::ZERO, self);
        }
        if rhs.fits_u64() && self.fits_u64() {
            return (
                U256::from_u64(self.0[0] / rhs.0[0]),
                U256::from_u64(self.0[0] % rhs.0[0]),
            );
        }
        if rhs.fits_u64() {
            let d = rhs.0[0] as u128;
            let mut q = [0u64; 4];
            let mut rem = 0u128;
            for i in (0..4).rev() {
                let cur = (rem << 64) | self.0[i] as u128;
                q[i] = (cur / d) as u64;
                rem = cur % d;
            }
            return (U256(q), U256::from_u64(rem as u64));
        }
        let shift = rhs.leading_zeros() - self.leading_zeros();
        let mut divisor = rhs << shift;
        let mut q = U256::ZERO;
        let mut rem = self;
        for _ in 0..=shift {
            q = q << 1;
            if rem >= divisor {
                rem = rem.wrapping_sub(divisor);
                q.0[0] |= 1;
            }
            divisor = divisor >> 1;
        }
        (q, rem)
    }

    pub fn is_negative(&self) -> bool {
        self.bit(255)
    }
    // -2^255 maps to itself. 2^255 is not representable.
    pub fn abs(self) -> U256 {
        if self.is_negative() {
            -self
        } else {
            self
        }
    }
    pub fn sdiv(self, rhs: U256) -> U256 {
        if rhs.is_zero() {
            return U256::ZERO;
        }
        let min = U256::ONE << 255;
        if self == min && rhs == U256::MAX {
            return min;
        }
        let q = self.abs() / rhs.abs();
        if self.is_negative() != rhs.is_negative() {
            -q
        } else {
            q
        }
    }
    pub fn smod(self, rhs: U256) -> U256 {
        if rhs.is_zero() {
            return U256::ZERO;
        }
        let r = self.abs() % rhs.abs();
        if self.is_negative() {
            -r
        } else {
            r
        }
    }
    pub fn scmp(&self, other: &U256) -> Ordering {
        match (self.is_negative(), other.is_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => self.cmp(other),
        }
    }
    pub fn addmod(self, b: U256, m: U256) -> U256 {
        if m.is_zero() {
            return U256::ZERO;
        }
        let (s, carry) = self.overflowing_add(b);
        if !carry {
            return s % m;
        }
        let two256_mod = ((U256::MAX % m).wrapping_add(U256::ONE)) % m;
        let sm = s % m;
        let (t, c) = two256_mod.overflowing_add(sm);
        if c || t >= m {
            t.wrapping_sub(m)
        } else {
            t
        }
    }
    pub fn mulmod(self, b: U256, m: U256) -> U256 {
        if m.is_zero() {
            return U256::ZERO;
        }
        let (lo, hi) = self.full_mul(b);
        if hi.is_zero() {
            return lo % m;
        }
        let mut rem = U256::ZERO;
        for i in (0..512).rev() {
            let bit = if i >= 256 { hi.bit(i - 256) } else { lo.bit(i) };
            let (r2, carry) = rem.overflowing_add(rem);
            let (r3, carry2) = r2.overflowing_add(U256::from_u64(bit as u64));
            rem = r3;
            if carry || carry2 || rem >= m {
                rem = rem.wrapping_sub(m);
            }
        }
        rem
    }
    pub fn pow(self, mut exp: U256) -> U256 {
        let mut base = self;
        let mut acc = U256::ONE;
        while !exp.is_zero() {
            if exp.0[0] & 1 == 1 {
                acc = acc.wrapping_mul(base);
            }
            exp = exp >> 1;
            if !exp.is_zero() {
                base = base.wrapping_mul(base);
            }
        }
        acc
    }
    pub fn signextend(b: U256, x: U256) -> U256 {
        if b >= U256::from_u64(31) {
            return x;
        }
        let bit = (b.low_u64() as u32) * 8 + 7;
        if x.bit(bit) {
            x | (U256::MAX << (bit + 1))
        } else {
            x & ((U256::ONE << (bit + 1)).wrapping_sub(U256::ONE))
        }
    }
    pub fn byte(i: U256, x: U256) -> U256 {
        if i >= U256::from_u64(32) {
            return U256::ZERO;
        }
        let bytes = x.to_be_bytes();
        U256::from_u64(bytes[i.low_u64() as usize] as u64)
    }

    pub fn to_hex(&self) -> String {
        if self.is_zero() {
            return "0x0".into();
        }
        let bytes = self.to_be_bytes();
        let mut s = String::from("0x");
        let mut started = false;
        for b in bytes {
            if !started {
                if b == 0 {
                    continue;
                }
                started = true;
                s.push_str(&format!("{:x}", b));
            } else {
                s.push_str(&format!("{:02x}", b));
            }
        }
        s
    }
    pub fn to_hex_padded(&self, bytes: usize) -> String {
        let b = self.to_be_bytes();
        let mut s = String::from("0x");
        for x in &b[32 - bytes.min(32)..] {
            s.push_str(&format!("{:02x}", x));
        }
        s
    }
    pub fn to_decimal(&self) -> String {
        if self.is_zero() {
            return "0".into();
        }
        let mut digits = Vec::new();
        let mut v = *self;
        let ten = U256::from_u64(10_000_000_000_000_000_000);
        while !v.is_zero() {
            let (q, r) = v.div_rem(ten);
            digits.push(r.low_u64());
            v = q;
        }
        let mut s = String::new();
        for (i, d) in digits.iter().rev().enumerate() {
            if i == 0 {
                s.push_str(&d.to_string());
            } else {
                s.push_str(&format!("{:019}", d));
            }
        }
        s
    }
    pub fn from_dec_str(s: &str) -> Option<U256> {
        let mut v = U256::ZERO;
        for c in s.bytes() {
            if !c.is_ascii_digit() {
                return None;
            }
            v = v
                .wrapping_mul(U256::from_u64(10))
                .wrapping_add(U256::from_u64((c - b'0') as u64));
        }
        Some(v)
    }
    pub fn from_hex_str(s: &str) -> Option<U256> {
        let s = s.strip_prefix("0x").unwrap_or(s);
        if s.is_empty() || s.len() > 64 {
            return None;
        }
        let mut v = U256::ZERO;
        for c in s.bytes() {
            let d = (c as char).to_digit(16)? as u64;
            v = (v << 4) | U256::from_u64(d);
        }
        Some(v)
    }
}

impl PartialOrd for U256 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for U256 {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..4).rev() {
            match self.0[i].cmp(&other.0[i]) {
                Ordering::Equal => continue,
                o => return o,
            }
        }
        Ordering::Equal
    }
}
impl std::ops::BitAnd for U256 {
    type Output = U256;
    fn bitand(self, r: U256) -> U256 {
        U256([
            self.0[0] & r.0[0],
            self.0[1] & r.0[1],
            self.0[2] & r.0[2],
            self.0[3] & r.0[3],
        ])
    }
}
impl std::ops::BitOr for U256 {
    type Output = U256;
    fn bitor(self, r: U256) -> U256 {
        U256([
            self.0[0] | r.0[0],
            self.0[1] | r.0[1],
            self.0[2] | r.0[2],
            self.0[3] | r.0[3],
        ])
    }
}
impl std::ops::BitXor for U256 {
    type Output = U256;
    fn bitxor(self, r: U256) -> U256 {
        U256([
            self.0[0] ^ r.0[0],
            self.0[1] ^ r.0[1],
            self.0[2] ^ r.0[2],
            self.0[3] ^ r.0[3],
        ])
    }
}
impl std::ops::Not for U256 {
    type Output = U256;
    fn not(self) -> U256 {
        U256([!self.0[0], !self.0[1], !self.0[2], !self.0[3]])
    }
}
impl std::ops::Add for U256 {
    type Output = U256;
    fn add(self, r: U256) -> U256 {
        self.wrapping_add(r)
    }
}
impl std::ops::Sub for U256 {
    type Output = U256;
    fn sub(self, r: U256) -> U256 {
        self.wrapping_sub(r)
    }
}
impl std::ops::Mul for U256 {
    type Output = U256;
    fn mul(self, r: U256) -> U256 {
        self.wrapping_mul(r)
    }
}
impl From<u64> for U256 {
    fn from(v: u64) -> U256 {
        U256::from_u64(v)
    }
}
impl From<usize> for U256 {
    fn from(v: usize) -> U256 {
        U256::from_u64(v as u64)
    }
}
impl From<u32> for U256 {
    fn from(v: u32) -> U256 {
        U256::from_u64(v as u64)
    }
}
impl From<bool> for U256 {
    fn from(v: bool) -> U256 {
        U256::from_u64(v as u64)
    }
}
impl fmt::Debug for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}
impl fmt::Display for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}
impl fmt::LowerHex for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.to_hex()[2..])
    }
}

impl std::ops::Shl<u32> for U256 {
    type Output = U256;
    fn shl(self, n: u32) -> U256 {
        if n >= 256 {
            return U256::ZERO;
        }
        let limb = (n / 64) as usize;
        let bits = n % 64;
        let mut r = [0u64; 4];
        for i in (limb..4).rev() {
            let src = i - limb;
            r[i] = self.0[src] << bits;
            if bits != 0 && src > 0 {
                r[i] |= self.0[src - 1] >> (64 - bits);
            }
        }
        U256(r)
    }
}

impl std::ops::Shr<u32> for U256 {
    type Output = U256;
    fn shr(self, n: u32) -> U256 {
        if n >= 256 {
            return U256::ZERO;
        }
        let limb = (n / 64) as usize;
        let bits = n % 64;
        let mut r = [0u64; 4];
        for (i, out) in r.iter_mut().enumerate().take(4 - limb) {
            let src = i + limb;
            *out = self.0[src] >> bits;
            if bits != 0 && src + 1 < 4 {
                *out |= self.0[src + 1] << (64 - bits);
            }
        }
        U256(r)
    }
}

impl std::ops::Div for U256 {
    type Output = U256;
    fn div(self, rhs: U256) -> U256 {
        self.div_rem(rhs).0
    }
}

impl std::ops::Rem for U256 {
    type Output = U256;
    fn rem(self, rhs: U256) -> U256 {
        self.div_rem(rhs).1
    }
}

impl std::ops::Neg for U256 {
    type Output = U256;
    fn neg(self) -> U256 {
        (!self).wrapping_add(U256::ONE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> U256 {
        U256::from_hex_str(s).unwrap()
    }

    #[test]
    fn arithmetic_roundtrip() {
        let a = u("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        assert_eq!(a.wrapping_add(U256::ONE), U256::ZERO);
        assert_eq!(U256::ZERO.wrapping_sub(U256::ONE), a);
        let b = u("0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        let c = u("0xfedcba9876543210");
        let (q, r) = b.div_rem(c);
        assert_eq!(q.wrapping_mul(c).wrapping_add(r), b);
        assert!(r < c);
        let (q2, r2) = b.div_rem(U256::ONE << 128);
        assert_eq!(q2, (b >> 128));
        assert_eq!(r2, b & (U256::ONE << 128).wrapping_sub(U256::ONE));
        let big = u("0xf000000000000000000000000000000000000000000000000000000000000001");
        let (q3, r3) = big.div_rem(u(
            "0x7000000000000000000000000000000000000000000000000000000000000000",
        ));
        assert_eq!(q3, U256::from_u64(2));
        assert_eq!(
            r3,
            u("0x1000000000000000000000000000000000000000000000000000000000000001")
        );
        assert_eq!(b.div_rem(U256::ZERO), (U256::ZERO, U256::ZERO));
    }

    #[test]
    fn shifts_and_signed() {
        let x = u("0x8000000000000000000000000000000000000000000000000000000000000000");
        assert_eq!((x >> 255), U256::ONE);
        assert_eq!(x.sar(255), U256::MAX);
        assert_eq!((U256::ONE << 255), x);
        assert_eq!((x << 1), U256::ZERO);
        assert_eq!(U256::MAX.sdiv(U256::from_u64(2)), U256::ZERO);
        assert_eq!((-U256::MAX), U256::ONE);
        assert_eq!(
            (-U256::from_u64(7)).sdiv(U256::from_u64(2)),
            (-U256::from_u64(3))
        );
        assert_eq!((-U256::from_u64(7)).smod(U256::from_u64(3)), (-U256::ONE));
        assert_eq!(
            U256::signextend(U256::ZERO, U256::from_u64(0xff)),
            U256::MAX
        );
        assert_eq!(
            U256::signextend(U256::ZERO, U256::from_u64(0x7f)),
            U256::from_u64(0x7f)
        );
        assert_eq!(
            U256::byte(U256::from_u64(31), U256::from_u64(0xab)),
            U256::from_u64(0xab)
        );
        assert_eq!(U256::byte(U256::ZERO, U256::from_u64(0xab)), U256::ZERO);
    }

    #[test]
    fn modular() {
        let m = u("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01");
        assert_eq!(
            U256::MAX.addmod(U256::MAX, m),
            ((U256::MAX % m).wrapping_add(U256::MAX % m) % m)
        );
        let x = U256::ONE << 255;
        assert_eq!(x.mulmod(x, x.wrapping_add(U256::ONE)), U256::ONE);
        assert_eq!(
            U256::from_u64(3).pow(U256::from_u64(5)),
            U256::from_u64(243)
        );
        assert_eq!(U256::from_u64(2).pow(U256::from_u64(256)), U256::ZERO);
    }

    #[test]
    fn strings() {
        let v = u("0xde0b6b3a7640000");
        assert_eq!(v.to_decimal(), "1000000000000000000");
        assert_eq!(U256::from_dec_str("1000000000000000000").unwrap(), v);
        assert_eq!(v.to_hex(), "0xde0b6b3a7640000");
        assert_eq!(U256::from_be_bytes(&v.to_be_bytes()), v);
        assert!(u("0xffffffffffffffffffffffffffffffffffffffff").is_low_mask());
        assert!(!u("0xffffffffffffffffffffffffffffffffffffff00").is_low_mask());
    }
}
