use crate::world::{Addr, Source};
use evmdec::rpc::{addr_to_string, Client};
use evmdec::U256;
use std::cell::RefCell;
use std::collections::HashMap;

pub struct Node {
    client: Client,
    failed: RefCell<(u64, String)>,
}

impl Node {
    #[must_use]
    pub fn new(client: Client) -> Node {
        Node {
            client,
            failed: RefCell::default(),
        }
    }

    fn read<T>(&self, answer: Result<T, String>) -> Option<T> {
        answer
            .map_err(|why| {
                let mut failed = self.failed.borrow_mut();
                if failed.0 == 0 {
                    failed.1 = why;
                }
                failed.0 += 1;
            })
            .ok()
    }

    #[must_use]
    pub fn trouble(&self) -> Option<String> {
        let (count, first) = &*self.failed.borrow();
        (*count > 0).then(|| {
            format!(
                "{count} reads of the chain's state got no answer and were taken to hold nothing. The first failed with: {first}"
            )
        })
    }
}

impl Source for Node {
    fn storage(&self, address: Addr, slot: U256) -> Option<U256> {
        let answer = self
            .client
            .get_storage(&addr_to_string(address), &slot.to_hex_padded(32));
        self.read(answer)
    }

    fn code(&self, address: Addr) -> Option<Vec<u8>> {
        self.read(self.client.get_code(&addr_to_string(address)))
    }

    fn balance(&self, address: Addr) -> Option<U256> {
        self.read(self.client.get_balance(&addr_to_string(address)))
    }
}

#[derive(Default)]
pub struct Table {
    pub storage: HashMap<(Addr, U256), U256>,
    pub codes: HashMap<Addr, Vec<u8>>,
    pub ether: HashMap<Addr, U256>,
}

impl Source for Table {
    fn storage(&self, address: Addr, slot: U256) -> Option<U256> {
        Some(
            self.storage
                .get(&(address, slot))
                .copied()
                .unwrap_or(U256::ZERO),
        )
    }

    fn code(&self, address: Addr) -> Option<Vec<u8>> {
        Some(self.codes.get(&address).cloned().unwrap_or_default())
    }

    fn balance(&self, address: Addr) -> Option<U256> {
        Some(self.ether.get(&address).copied().unwrap_or(U256::ZERO))
    }
}
