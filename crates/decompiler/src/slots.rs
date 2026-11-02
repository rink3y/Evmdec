//! Names for storage slots that standards and widely used libraries fix in advance.
//!
//! A proxy keeps its implementation at `keccak256("eip1967.proxy.implementation") - 1`, a
//! diamond its routing table at `keccak256("diamond.standard.diamond.storage")`, an
//! OpenZeppelin 5 contract its state under ERC-7201 namespaces. Such a slot is a 32-byte
//! constant in the bytecode; naming it says what the variable is without any guess about the
//! contract. Every slot here is derived from its label at first use, so no hash is written down.

use crate::keccak::keccak256;
use crate::u256::U256;
use std::collections::HashMap;
use std::sync::OnceLock;

/// How a label becomes a slot.
#[derive(Clone, Copy)]
enum Scheme {
    /// `keccak256(label) - 1` (EIP-1967).
    HashMinusOne,
    /// `keccak256(label)` (diamond storage, ZeppelinOS).
    Hash,
    /// `keccak256(uint256(keccak256(label)) - 1) & ~0xff` (ERC-7201), plus a member offset.
    Erc7201(u64),
}

/// `(label, scheme, name)`.
const KNOWN: &[(&str, Scheme, &str)] = &[
    (
        "eip1967.proxy.implementation",
        Scheme::HashMinusOne,
        "eip1967_implementation",
    ),
    ("eip1967.proxy.admin", Scheme::HashMinusOne, "eip1967_admin"),
    (
        "eip1967.proxy.beacon",
        Scheme::HashMinusOne,
        "eip1967_beacon",
    ),
    (
        "eip1967.proxy.rollback",
        Scheme::HashMinusOne,
        "eip1967_rollback",
    ),
    (
        "org.zeppelinos.proxy.implementation",
        Scheme::Hash,
        "zeppelinos_implementation",
    ),
    (
        "org.zeppelinos.proxy.admin",
        Scheme::Hash,
        "zeppelinos_admin",
    ),
    (
        "diamond.standard.diamond.storage",
        Scheme::Hash,
        "diamond_storage",
    ),
    (
        "openzeppelin.storage.Initializable",
        Scheme::Erc7201(0),
        "oz_initializable",
    ),
    (
        "openzeppelin.storage.Ownable",
        Scheme::Erc7201(0),
        "oz_ownable",
    ),
    (
        "openzeppelin.storage.Ownable2Step",
        Scheme::Erc7201(0),
        "oz_pending_owner",
    ),
    (
        "openzeppelin.storage.ReentrancyGuard",
        Scheme::Erc7201(0),
        "oz_reentrancy_status",
    ),
    (
        "openzeppelin.storage.Pausable",
        Scheme::Erc7201(0),
        "oz_paused",
    ),
    (
        "openzeppelin.storage.AccessControl",
        Scheme::Erc7201(0),
        "oz_roles",
    ),
    (
        "openzeppelin.storage.ERC20",
        Scheme::Erc7201(0),
        "oz_erc20_balances",
    ),
    (
        "openzeppelin.storage.ERC20",
        Scheme::Erc7201(1),
        "oz_erc20_allowances",
    ),
    (
        "openzeppelin.storage.ERC20",
        Scheme::Erc7201(2),
        "oz_erc20_total_supply",
    ),
    (
        "openzeppelin.storage.ERC20",
        Scheme::Erc7201(3),
        "oz_erc20_name",
    ),
    (
        "openzeppelin.storage.ERC20",
        Scheme::Erc7201(4),
        "oz_erc20_symbol",
    ),
    (
        "openzeppelin.storage.Nonces",
        Scheme::Erc7201(0),
        "oz_nonces",
    ),
    (
        "openzeppelin.storage.EIP712",
        Scheme::Erc7201(0),
        "oz_eip712_name",
    ),
    (
        "openzeppelin.storage.EIP712",
        Scheme::Erc7201(1),
        "oz_eip712_version",
    ),
];

/// The slot a label and scheme name.
fn slot_of(label: &str, scheme: Scheme) -> U256 {
    let h = U256::from_be_bytes(&keccak256(label.as_bytes()));
    match scheme {
        Scheme::Hash => h,
        Scheme::HashMinusOne => h - U256::ONE,
        Scheme::Erc7201(offset) => {
            let inner = (h - U256::ONE).to_be_bytes();
            let base = U256::from_be_bytes(&keccak256(&inner)) & !U256::from_u64(0xff);
            base + U256::from_u64(offset)
        }
    }
}

/// The name of a well-known storage slot, if `slot` is one.
pub fn well_known(slot: U256) -> Option<&'static str> {
    static TABLE: OnceLock<HashMap<U256, &'static str>> = OnceLock::new();
    TABLE
        .get_or_init(|| {
            KNOWN
                .iter()
                .map(|(label, scheme, name)| (slot_of(label, *scheme), *name))
                .collect()
        })
        .get(&slot)
        .copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_slots_match_their_published_values() {
        let at = |hex: &str| U256::from_hex_str(hex).expect("hex");
        assert_eq!(
            well_known(at(
                "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"
            )),
            Some("eip1967_implementation")
        );
        assert_eq!(
            well_known(at(
                "0xc8fcad8db84d3cc18b4c41d551ea0ee66dd599cde068d998e57d5e09332c131c"
            )),
            Some("diamond_storage")
        );
        assert_eq!(
            well_known(at(
                "0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300"
            )),
            Some("oz_ownable")
        );
        assert_eq!(well_known(U256::ZERO), None);
    }
}
