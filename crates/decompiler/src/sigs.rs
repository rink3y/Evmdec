use crate::keccak;
use crate::sigdb;
use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::OnceLock;

#[derive(Debug)]
pub struct Sigs {
    pub functions: HashMap<u32, Vec<&'static str>>,
    pub events: HashMap<[u8; 32], &'static str>,
    pub errors: HashMap<u32, &'static str>,
}

static SIGS: OnceLock<Sigs> = OnceLock::new();

pub fn get() -> &'static Sigs {
    SIGS.get_or_init(|| {
        let mut functions: HashMap<u32, Vec<&'static str>> = HashMap::new();
        for s in FUNCTIONS {
            functions
                .entry(keccak::selector_u32(s))
                .or_default()
                .push(s);
        }
        let mut events = HashMap::new();
        for s in EVENTS {
            events.insert(keccak::keccak256(s.as_bytes()), *s);
        }
        let mut errors = HashMap::new();
        for s in ERRORS {
            errors.insert(keccak::selector_u32(s), *s);
        }
        Sigs {
            functions,
            events,
            errors,
        }
    })
}

pub fn function(selector: u32) -> Option<Cow<'static, str>> {
    if let Some(s) = get().functions.get(&selector).and_then(|v| v.first()) {
        return Some(Cow::Borrowed(s));
    }
    sigdb::global()
        .and_then(|db| db.selector(selector).into_iter().next())
        .map(Cow::Owned)
}

pub fn event(topic: &[u8; 32]) -> Option<Cow<'static, str>> {
    if let Some(s) = get().events.get(topic) {
        return Some(Cow::Borrowed(s));
    }
    sigdb::global()
        .and_then(|db| db.topic(topic))
        .map(Cow::Owned)
}

pub fn error(selector: u32) -> Option<Cow<'static, str>> {
    if let Some(s) = get().errors.get(&selector) {
        return Some(Cow::Borrowed(s));
    }
    sigdb::global()
        .and_then(|db| db.selector(selector).into_iter().next())
        .map(Cow::Owned)
}

// A lookup service is not trusted. Its names end up in the output and the report.
#[cfg(feature = "rpc")]
fn answers(sig: &str, selector: u32) -> bool {
    let plain = |c: char| c.is_ascii_alphanumeric() || "_$(),[]".contains(c);
    sig.chars().all(plain) && crate::keccak::selector(sig) == selector.to_be_bytes()
}

#[cfg(feature = "rpc")]
pub fn lookup_online(selectors: &[u32]) -> HashMap<u32, String> {
    let mut out = HashMap::new();
    let unknown: Vec<u32> = selectors
        .iter()
        .copied()
        .filter(|s| function(*s).is_none())
        .collect();
    if unknown.is_empty() {
        return out;
    }
    let agent = ureq::AgentBuilder::new()
        .timeout(std::time::Duration::from_secs(15))
        .build();
    for chunk in unknown.chunks(50) {
        let q: Vec<String> = chunk.iter().map(|s| format!("{:#010x}", s)).collect();
        let url = format!(
            "https://api.openchain.xyz/signature-database/v1/lookup?function={}&filter=true",
            q.join(",")
        );
        if let Ok(resp) = agent.get(&url).call() {
            if let Ok(v) = resp.into_json::<serde_json::Value>() {
                if let Some(map) = v.pointer("/result/function").and_then(|m| m.as_object()) {
                    for (k, arr) in map {
                        if let (Ok(sel), Some(first)) = (
                            u32::from_str_radix(k.trim_start_matches("0x"), 16),
                            arr.as_array()
                                .and_then(|a| a.first())
                                .and_then(|e| e.get("name"))
                                .and_then(|n| n.as_str()),
                        ) {
                            if answers(first, sel) {
                                out.insert(sel, first.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    for sel in unknown {
        if out.contains_key(&sel) {
            continue;
        }
        let url = format!("https://www.4byte.directory/api/v1/signatures/?hex_signature={:#010x}&ordering=created_at", sel);
        if let Ok(resp) = agent.get(&url).call() {
            if let Ok(v) = resp.into_json::<serde_json::Value>() {
                if let Some(t) = v
                    .pointer("/results/0/text_signature")
                    .and_then(|x| x.as_str())
                {
                    if answers(t, sel) {
                        out.insert(sel, t.to_string());
                    }
                }
            }
        }
    }
    out
}

pub fn name_of(sig: &str) -> &str {
    sig.split('(').next().unwrap_or(sig)
}

pub fn params_of(sig: &str) -> Vec<String> {
    let inner = match (sig.find('('), sig.rfind(')')) {
        (Some(a), Some(b)) if b > a => &sig[a + 1..b],
        _ => return vec![],
    };
    let mut out = Vec::new();
    let mut depth = 0;
    let mut cur = String::new();
    for c in inner.chars() {
        match c {
            '(' => {
                depth += 1;
                cur.push(c);
            }
            ')' => {
                depth -= 1;
                cur.push(c);
            }
            ',' if depth == 0 => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

pub const FUNCTIONS: &[&str] = &[
    "name()", "symbol()", "decimals()", "totalSupply()", "balanceOf(address)", "transfer(address,uint256)", "transferFrom(address,address,uint256)",
    "approve(address,uint256)", "allowance(address,address)", "increaseAllowance(address,uint256)", "decreaseAllowance(address,uint256)",
    "mint(address,uint256)", "mint(uint256)", "burn(uint256)", "burn(address,uint256)", "burnFrom(address,uint256)", "mintTo(address,uint256)",
    "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", "nonces(address)", "DOMAIN_SEPARATOR()", "PERMIT_TYPEHASH()",
    "cap()", "version()", "deposit()", "withdraw(uint256)", "withdraw(address,uint256)", "withdrawTo(address,uint256)", "flush()",
    "transferAndCall(address,uint256,bytes)", "approveAndCall(address,uint256,bytes)", "transferWithAuthorization(address,address,uint256,uint256,uint256,bytes32,uint8,bytes32,bytes32)",
    "receiveWithAuthorization(address,address,uint256,uint256,uint256,bytes32,uint8,bytes32,bytes32)", "cancelAuthorization(address,bytes32,uint8,bytes32,bytes32)", "authorizationState(address,bytes32)",
    "issue(uint256)", "redeem(uint256)", "deprecate(address)", "deprecated()", "upgradedAddress()", "basisPointsRate()", "maximumFee()", "MAX_UINT()",
    "setParams(uint256,uint256)", "addBlackList(address)", "removeBlackList(address)", "destroyBlackFunds(address)", "getBlackListStatus(address)", "isBlackListed(address)",
    "pause()", "unpause()", "paused()", "pauser()", "updatePauser(address)", "blacklister()", "updateBlacklister(address)", "blacklist(address)", "unBlacklist(address)", "isBlacklisted(address)",
    "masterMinter()", "updateMasterMinter(address)", "configureMinter(address,uint256)", "removeMinter(address)", "isMinter(address)", "minterAllowance(address)", "currency()",
    "initialize(string,string,string,uint8,address,address,address,address)", "initializeV2(string)", "initializeV2_1(address)", "initializeV2_2(address[],string)", "rescuer()", "updateRescuer(address)", "rescueERC20(address,address,uint256)",
    "owner()", "transferOwnership(address)", "renounceOwnership()", "acceptOwnership()", "pendingOwner()", "getOwner()", "admin()", "setAdmin(address)", "changeAdmin(address)", "pendingAdmin()", "acceptAdmin()",
    "hasRole(bytes32,address)", "getRoleAdmin(bytes32)", "grantRole(bytes32,address)", "revokeRole(bytes32,address)", "renounceRole(bytes32,address)", "DEFAULT_ADMIN_ROLE()", "getRoleMember(bytes32,uint256)", "getRoleMemberCount(bytes32)",
    "MINTER_ROLE()", "PAUSER_ROLE()", "BURNER_ROLE()", "isOwner()", "owners()", "addOwner(address)", "removeOwner(address)", "nominateNewOwner(address)", "nominatedOwner()",
    "supportsInterface(bytes4)", "ownerOf(uint256)", "safeTransferFrom(address,address,uint256)", "safeTransferFrom(address,address,uint256,bytes)", "getApproved(uint256)", "setApprovalForAll(address,bool)", "isApprovedForAll(address,address)",
    "tokenURI(uint256)", "baseURI()", "setBaseURI(string)", "tokenByIndex(uint256)", "tokenOfOwnerByIndex(address,uint256)", "exists(uint256)", "safeMint(address,uint256)", "safeMint(address)",
    "balanceOf(address,uint256)", "balanceOfBatch(address[],uint256[])", "safeTransferFrom(address,address,uint256,uint256,bytes)", "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)", "uri(uint256)",
    "onERC721Received(address,address,uint256,bytes)", "onERC1155Received(address,address,uint256,uint256,bytes)", "onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)", "tokensReceived(address,address,address,uint256,bytes,bytes)",
    "royaltyInfo(uint256,uint256)", "contractURI()", "totalMinted()", "maxSupply()", "price()", "setPrice(uint256)", "mintPrice()", "whitelistMint(uint256,bytes32[])", "publicMint(uint256)", "reveal()", "setMerkleRoot(bytes32)", "merkleRoot()",
    "asset()", "totalAssets()", "convertToShares(uint256)", "convertToAssets(uint256)", "maxDeposit(address)", "previewDeposit(uint256)", "deposit(uint256,address)", "maxMint(address)", "previewMint(uint256)", "mint(uint256,address)",
    "maxWithdraw(address)", "previewWithdraw(uint256)", "withdraw(uint256,address,address)", "maxRedeem(address)", "previewRedeem(uint256)", "redeem(uint256,address,address)",
    "implementation()", "upgradeTo(address)", "upgradeToAndCall(address,bytes)", "proxiableUUID()", "changeAdmin(address)", "admin()", "proxyType()", "isDepositable()", "proxy_getIsDepositable()",
    "getImplementation()", "getAdmin()", "upgrade(address,address)", "upgradeAndCall(address,address,bytes)", "getProxyImplementation(address)", "getProxyAdmin(address)", "changeProxyAdmin(address,address)",
    "beacon()", "setBeacon(address)", "masterCopy()", "initialize(address,bytes)", "initialize(address)", "initialize()", "initialize(address,address)", "initialize(uint256)", "initialized()",
    "paused()", "pause()", "unpause()", "setPaused(bool)", "kill()", "destroy()", "selfDestruct()", "emergencyWithdraw()", "emergencyWithdraw(address)", "rescueTokens(address,uint256)", "sweep(address)", "recoverERC20(address,uint256)",
    "multicall(bytes[])", "multicall(uint256,bytes[])", "multicall(bytes32,bytes[])", "aggregate((address,bytes)[])", "tryAggregate(bool,(address,bytes)[])", "tryBlockAndAggregate(bool,(address,bytes)[])", "blockAndAggregate((address,bytes)[])",
    "aggregate3((address,bool,bytes)[])", "aggregate3Value((address,bool,uint256,bytes)[])", "getBlockHash(uint256)", "getBlockNumber()", "getCurrentBlockCoinbase()", "getCurrentBlockDifficulty()", "getCurrentBlockGasLimit()", "getCurrentBlockTimestamp()", "getEthBalance(address)", "getLastBlockHash()", "getBasefee()", "getChainId()",
    "isValidSignature(bytes32,bytes)", "isValidSignature(bytes,bytes)", "eip712Domain()", "nonce()", "execute(address,uint256,bytes)", "executeBatch(address[],bytes[])", "executeBatch(address[],uint256[],bytes[])", "entryPoint()", "validateUserOp((address,uint256,bytes,bytes,bytes32,uint256,bytes32,bytes,bytes),bytes32,uint256)",
    "deposit()", "withdraw(uint256)",
    "factory()", "WETH()", "token0()", "token1()", "getReserves()", "price0CumulativeLast()", "price1CumulativeLast()", "kLast()", "MINIMUM_LIQUIDITY()", "sync()", "skim(address)", "burn(address)", "swap(uint256,uint256,address,bytes)", "initialize(address,address)",
    "getPair(address,address)", "allPairs(uint256)", "allPairsLength()", "createPair(address,address)", "feeTo()", "feeToSetter()", "setFeeTo(address)", "setFeeToSetter(address)",
    "addLiquidity(address,address,uint256,uint256,uint256,uint256,address,uint256)", "addLiquidityETH(address,uint256,uint256,uint256,address,uint256)", "removeLiquidity(address,address,uint256,uint256,uint256,address,uint256)",
    "removeLiquidityETH(address,uint256,uint256,uint256,address,uint256)", "removeLiquidityWithPermit(address,address,uint256,uint256,uint256,address,uint256,bool,uint8,bytes32,bytes32)", "removeLiquidityETHWithPermit(address,uint256,uint256,uint256,address,uint256,bool,uint8,bytes32,bytes32)",
    "removeLiquidityETHSupportingFeeOnTransferTokens(address,uint256,uint256,uint256,address,uint256)", "removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(address,uint256,uint256,uint256,address,uint256,bool,uint8,bytes32,bytes32)",
    "swapExactTokensForTokens(uint256,uint256,address[],address,uint256)", "swapTokensForExactTokens(uint256,uint256,address[],address,uint256)", "swapExactETHForTokens(uint256,address[],address,uint256)", "swapTokensForExactETH(uint256,uint256,address[],address,uint256)",
    "swapExactTokensForETH(uint256,uint256,address[],address,uint256)", "swapETHForExactTokens(uint256,address[],address,uint256)", "swapExactTokensForTokensSupportingFeeOnTransferTokens(uint256,uint256,address[],address,uint256)",
    "swapExactETHForTokensSupportingFeeOnTransferTokens(uint256,address[],address,uint256)", "swapExactTokensForETHSupportingFeeOnTransferTokens(uint256,uint256,address[],address,uint256)",
    "quote(uint256,uint256,uint256)", "getAmountOut(uint256,uint256,uint256)", "getAmountIn(uint256,uint256,uint256)", "getAmountsOut(uint256,address[])", "getAmountsIn(uint256,address[])", "uniswapV2Call(address,uint256,uint256,bytes)",
    "createPool(address,address,uint24)", "getPool(address,address,uint24)", "feeAmountTickSpacing(uint24)", "enableFeeAmount(uint24,int24)", "setOwner(address)", "parameters()",
    "slot0()", "liquidity()", "fee()", "tickSpacing()", "maxLiquidityPerTick()", "ticks(int24)", "tickBitmap(int16)", "positions(bytes32)", "observations(uint256)", "feeGrowthGlobal0X128()", "feeGrowthGlobal1X128()", "protocolFees()",
    "mint(address,int24,int24,uint128,bytes)", "burn(int24,int24,uint128)", "collect(address,int24,int24,uint128,uint128)", "swap(address,bool,int256,uint160,bytes)", "flash(address,uint256,uint256,bytes)", "observe(uint32[])", "increaseObservationCardinalityNext(uint16)", "initialize(uint160)",
    "uniswapV3SwapCallback(int256,int256,bytes)", "uniswapV3MintCallback(uint256,uint256,bytes)", "uniswapV3FlashCallback(uint256,uint256,bytes)",
    "exactInputSingle((address,address,uint24,address,uint256,uint256,uint256,uint160))", "exactInput((bytes,address,uint256,uint256,uint256))", "exactOutputSingle((address,address,uint24,address,uint256,uint256,uint256,uint160))", "exactOutput((bytes,address,uint256,uint256,uint256))",
    "exactInputSingle((address,address,uint24,address,uint256,uint256,uint160))", "exactInput((bytes,address,uint256,uint256))", "exactOutputSingle((address,address,uint24,address,uint256,uint256,uint160))", "exactOutput((bytes,address,uint256,uint256))",
    "WETH9()", "refundETH()", "unwrapWETH9(uint256,address)", "sweepToken(address,uint256,address)", "selfPermit(address,uint256,uint256,uint8,bytes32,bytes32)", "selfPermitAllowed(address,uint256,uint256,uint8,bytes32,bytes32)", "wrapETH(uint256)",
    "swapExactTokensForTokens(uint256,uint256,address[],address)", "swapTokensForExactTokens(uint256,uint256,address[],address)", "approveMax(address)", "approveZeroThenMax(address)", "pull(address,uint256)", "sweepTokenWithFee(address,uint256,address,uint256,address)",
    "execute(bytes,bytes[])", "execute(bytes,bytes[],uint256)", "collectRewards(bytes)",
    "allowance(address,address,address)", "approve(address,address,uint160,uint48)", "permit(address,((address,uint160,uint48,uint48),address,uint256),bytes)", "permit(address,((address,uint160,uint48,uint48)[],address,uint256),bytes)",
    "transferFrom(address,address,uint160,address)", "transferFrom((address,address,uint160,address)[])", "lockdown((address,address)[])", "invalidateNonces(address,address,uint48)", "invalidateUnorderedNonces(uint256,uint256)", "nonceBitmap(address,uint256)",
    "permitTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes)", "permitTransferFrom(((address,uint256)[],uint256,uint256),(address,uint256)[],address,bytes)",
    "permitWitnessTransferFrom(((address,uint256),uint256,uint256),(address,uint256),address,bytes32,string,bytes)", "permitWitnessTransferFrom(((address,uint256)[],uint256,uint256),(address,uint256)[],address,bytes32,string,bytes)",
    "setup(address[],uint256,address,bytes,address,address,uint256,address)", "execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)", "getOwners()", "getThreshold()", "isOwner(address)", "nonce()",
    "addOwnerWithThreshold(address,uint256)", "removeOwner(address,address,uint256)", "swapOwner(address,address,address)", "changeThreshold(uint256)", "enableModule(address)", "disableModule(address,address)", "isModuleEnabled(address)", "getModulesPaginated(address,uint256)",
    "execTransactionFromModule(address,uint256,bytes,uint8)", "execTransactionFromModuleReturnData(address,uint256,bytes,uint8)", "setGuard(address)", "setFallbackHandler(address)", "approveHash(bytes32)", "approvedHashes(address,bytes32)", "signedMessages(bytes32)",
    "getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)", "encodeTransactionData(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)", "checkSignatures(bytes32,bytes,bytes)", "checkNSignatures(bytes32,bytes,bytes,uint256)",
    "domainSeparator()", "getChainId()", "getStorageAt(uint256,uint256)", "simulateAndRevert(address,bytes)", "requiredTxGas(address,uint256,bytes,uint8)", "getModules()", "VERSION()", "createProxyWithNonce(address,bytes,uint256)", "proxyCreationCode()",
    "mint()", "redeem(uint256)", "redeemUnderlying(uint256)", "borrow(uint256)", "repayBorrow()", "repayBorrow(uint256)", "repayBorrowBehalf(address)", "repayBorrowBehalf(address,uint256)", "liquidateBorrow(address,address)", "liquidateBorrow(address,uint256,address)",
    "exchangeRateCurrent()", "exchangeRateStored()", "getCash()", "accrueInterest()", "borrowBalanceCurrent(address)", "borrowBalanceStored(address)", "balanceOfUnderlying(address)", "getAccountSnapshot(address)", "borrowRatePerBlock()", "supplyRatePerBlock()",
    "totalBorrowsCurrent()", "totalBorrows()", "totalReserves()", "reserveFactorMantissa()", "accrualBlockNumber()", "borrowIndex()", "comptroller()", "interestRateModel()", "underlying()", "isCToken()", "seize(address,address,uint256)",
    "_setComptroller(address)", "_setReserveFactor(uint256)", "_reduceReserves(uint256)", "_setInterestRateModel(address)", "_setPendingAdmin(address)", "_acceptAdmin()", "_addReserves(uint256)", "pendingAdmin()", "initialExchangeRateMantissa()",
    "initialize(address,address,uint256,string,string,uint8)", "enterMarkets(address[])", "exitMarket(address)", "getAccountLiquidity(address)", "claimComp(address)", "markets(address)", "getAllMarkets()", "oracle()", "closeFactorMantissa()", "liquidationIncentiveMantissa()",
    "wards(address)", "rely(address)", "deny(address)", "live()", "cage()", "file(bytes32,uint256)", "file(bytes32,bytes32,uint256)", "file(bytes32,address)", "init(bytes32)", "ilks(bytes32)", "urns(bytes32,address)", "gem(bytes32,address)", "dai(address)", "sin(address)",
    "debt()", "vice()", "Line()", "can(address,address)", "hope(address)", "nope(address)", "slip(bytes32,address,int256)", "flux(bytes32,address,address,uint256)", "move(address,address,uint256)", "frob(bytes32,address,address,address,int256,int256)", "fork(bytes32,address,address,int256,int256)",
    "grab(bytes32,address,address,address,int256,int256)", "heal(uint256)", "suck(address,address,uint256)", "fold(bytes32,address,int256)", "vat()", "join(address,uint256)", "exit(address,uint256)", "drip(bytes32)", "poke(bytes32)",
    "supply(address,uint256,address,uint16)", "withdraw(address,uint256,address)", "borrow(address,uint256,uint256,uint16,address)", "repay(address,uint256,uint256,address)", "flashLoan(address,address[],uint256[],uint256[],address,bytes,uint16)", "flashLoanSimple(address,address,uint256,bytes,uint16)",
    "liquidationCall(address,address,address,uint256,bool)", "getUserAccountData(address)", "getReserveData(address)", "getReservesList()", "setUserUseReserveAsCollateral(address,bool)", "ADDRESSES_PROVIDER()", "POOL()", "getPool()", "getPriceOracle()", "getLendingPool()",
    "executeOperation(address[],uint256[],uint256[],address,bytes)", "executeOperation(address,uint256,uint256,address,bytes)", "deposit(address,uint256,address,uint16)", "swapBorrowRateMode(address,uint256)", "rebalanceStableBorrowRate(address,address)", "mintToTreasury(address[])",
    "resolver(bytes32)", "setResolver(bytes32,address)", "ttl(bytes32)", "setTTL(bytes32,uint64)", "setOwner(bytes32,address)", "owner(bytes32)", "setSubnodeOwner(bytes32,bytes32,address)", "setSubnodeRecord(bytes32,bytes32,address,address,uint64)", "setRecord(bytes32,address,address,uint64)", "recordExists(bytes32)", "old()",
    "addr(bytes32)", "setAddr(bytes32,address)", "name(bytes32)", "setName(bytes32,string)", "text(bytes32,string)", "contenthash(bytes32)", "available(uint256)", "available(string)", "nameExpires(uint256)", "register(string,address,uint256,bytes32)", "renew(string,uint256)", "rentPrice(string,uint256)", "commit(bytes32)", "makeCommitment(string,address,bytes32)",
    "submit(address)", "getTotalPooledEther()", "getPooledEthByShares(uint256)", "getSharesByPooledEth(uint256)", "sharesOf(address)", "getTotalShares()", "transferShares(address,uint256)", "stake()", "stake(uint256)", "unstake(uint256)", "claim()", "claimRewards()", "getReward()", "earned(address)", "rewardRate()", "rewardPerToken()", "notifyRewardAmount(uint256)", "stakingToken()", "rewardsToken()", "exit()",
    "propose(address[],uint256[],string[],bytes[],string)", "propose(address[],uint256[],bytes[],string)", "castVote(uint256,uint8)", "castVote(uint256,bool)", "castVoteWithReason(uint256,uint8,string)", "castVoteBySig(uint256,uint8,uint8,bytes32,bytes32)", "queue(uint256)", "execute(uint256)", "cancel(uint256)", "state(uint256)", "proposals(uint256)", "getActions(uint256)", "getReceipt(uint256,address)",
    "votingDelay()", "votingPeriod()", "proposalThreshold()", "quorumVotes()", "timelock()", "getVotes(address,uint256)", "getPastVotes(address,uint256)", "getPastTotalSupply(uint256)", "delegate(address)", "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", "delegates(address)", "getCurrentVotes(address)", "getPriorVotes(address,uint256)", "checkpoints(address,uint32)", "numCheckpoints(address)", "DELEGATION_TYPEHASH()", "minter()", "mintingAllowedAfter()", "setMinter(address)", "minimumTimeBetweenMints()", "mintCap()",
    "delay()", "GRACE_PERIOD()", "MINIMUM_DELAY()", "MAXIMUM_DELAY()", "queueTransaction(address,uint256,string,bytes,uint256)", "executeTransaction(address,uint256,string,bytes,uint256)", "cancelTransaction(address,uint256,string,bytes,uint256)", "queuedTransactions(bytes32)", "setDelay(uint256)",
    "A()", "A_precise()", "get_virtual_price()", "calc_token_amount(uint256[3],bool)", "calc_token_amount(uint256[2],bool)", "add_liquidity(uint256[3],uint256)", "add_liquidity(uint256[2],uint256)", "add_liquidity(uint256[2],uint256,address)", "get_dy(int128,int128,uint256)", "get_dy_underlying(int128,int128,uint256)", "get_dy(uint256,uint256,uint256)",
    "exchange(int128,int128,uint256,uint256)", "exchange(uint256,uint256,uint256,uint256)", "exchange(uint256,uint256,uint256,uint256,bool)", "exchange(uint256,uint256,uint256,uint256,bool,address)", "exchange_underlying(int128,int128,uint256,uint256)", "remove_liquidity(uint256,uint256[3])", "remove_liquidity(uint256,uint256[2])", "remove_liquidity_imbalance(uint256[3],uint256)", "remove_liquidity_imbalance(uint256[2],uint256)",
    "calc_withdraw_one_coin(uint256,int128)", "calc_withdraw_one_coin(uint256,uint256)", "remove_liquidity_one_coin(uint256,int128,uint256)", "remove_liquidity_one_coin(uint256,uint256,uint256)", "ramp_A(uint256,uint256)", "stop_ramp_A()", "commit_new_fee(uint256,uint256)", "apply_new_fee()", "revert_new_parameters()", "commit_transfer_ownership(address)", "apply_transfer_ownership()", "revert_transfer_ownership()",
    "admin_balances(uint256)", "withdraw_admin_fees()", "donate_admin_fees()", "kill_me()", "unkill_me()", "coins(uint256)", "balances(uint256)", "fee()", "admin_fee()", "owner()", "initial_A()", "future_A()", "initial_A_time()", "future_A_time()", "admin_actions_deadline()", "transfer_ownership_deadline()", "future_fee()", "future_admin_fee()", "future_owner()",
    "price_oracle()", "price_oracle(uint256)", "price_scale()", "price_scale(uint256)", "last_prices()", "last_prices(uint256)", "lp_price()", "virtual_price()", "D()", "gamma()", "mid_fee()", "out_fee()", "fee_gamma()", "allowed_extra_profit()", "adjustment_step()", "ma_time()", "xcp_profit()", "xcp_profit_a()", "claim_admin_fees()", "future_A_gamma()", "future_A_gamma_time()", "initial_A_gamma()", "initial_A_gamma_time()", "ramp_A_gamma(uint256,uint256,uint256)", "stop_ramp_A_gamma()", "commit_new_parameters(uint256,uint256,uint256,uint256,uint256,uint256)", "apply_new_parameters()", "set_admin_fee_receiver(address)", "fee_receiver()", "admin()", "factory()", "salt()", "precisions()", "packed_fee_params()", "packed_rebalancing_params()", "last_prices_timestamp()", "calc_token_fee(uint256[3],uint256[3])", "get_dx(uint256,uint256,uint256)", "calc_withdraw_one_coin(uint256,uint256)", "exchange_extended(uint256,uint256,uint256,uint256,bool,address,bytes32)", "exchange_received(uint256,uint256,uint256,uint256,bool,address)", "remove_liquidity(uint256,uint256[3],bool,address)", "add_liquidity(uint256[3],uint256,bool,address)", "remove_liquidity_one_coin(uint256,uint256,uint256,bool,address)", "token()", "lp_token()", "N_COINS()", "PRECISION()", "A_PRECISION()", "MAX_A()", "MAX_A_CHANGE()", "MIN_RAMP_TIME()",
    "swap(address,(address,address,address,address,uint256,uint256,uint256),bytes,bytes)", "unoswap(address,uint256,uint256,uint256[])", "unoswapTo(address,address,uint256,uint256,uint256[])", "uniswapV3Swap(uint256,uint256,uint256[])", "uniswapV3SwapTo(address,uint256,uint256,uint256[])", "clipperSwap(address,address,address,uint256,uint256,uint256,bytes32,bytes32)", "fillOrder((uint256,address,address,address,address,address,uint256,uint256,uint256,bytes),bytes,bytes,uint256,uint256,uint256)", "fillOrderRFQ((uint256,address,address,address,address,uint256,uint256),bytes,uint256)", "cancelOrder((uint256,address,address,address,address,address,uint256,uint256,uint256,bytes))", "remaining(bytes32)", "invalidatorForOrderRFQ(address,uint256)", "rescueFunds(address,uint256)", "destroy()", "hashOrder((uint256,address,address,address,address,address,uint256,uint256,uint256,bytes))", "checkPredicate((uint256,address,address,address,address,address,uint256,uint256,uint256,bytes))", "simulate(address,bytes)", "and(uint256,bytes)", "or(uint256,bytes)", "eq(uint256,bytes)", "lt(uint256,bytes)", "gt(uint256,bytes)", "arbitraryStaticCall(address,bytes)", "timestampBelow(uint256)", "nonce(address)", "advanceNonce(uint8)", "increaseNonce()", "nonceEquals(address,uint256)",
    "fulfillBasicOrder((address,uint256,uint256,address,address,address,uint256,uint256,uint8,uint256,uint256,bytes32,uint256,bytes32,bytes32,uint256,(uint256,address)[],bytes))", "fulfillOrder(((address,address,(uint8,address,uint256,uint256,uint256)[],(uint8,address,uint256,uint256,uint256,address)[],uint8,uint256,uint256,bytes32,uint256,bytes32,uint256),bytes),bytes32)",
    "fulfillAdvancedOrder(((address,address,(uint8,address,uint256,uint256,uint256)[],(uint8,address,uint256,uint256,uint256,address)[],uint8,uint256,uint256,bytes32,uint256,bytes32,uint256),uint120,uint120,bytes,bytes),(uint256,uint8,uint256,uint256,bytes32[])[],bytes32,address)", "cancel((address,address,(uint8,address,uint256,uint256,uint256)[],(uint8,address,uint256,uint256,uint256,address)[],uint8,uint256,uint256,bytes32,uint256,bytes32,uint256)[])", "validate(((address,address,(uint8,address,uint256,uint256,uint256)[],(uint8,address,uint256,uint256,uint256,address)[],uint8,uint256,uint256,bytes32,uint256,bytes32,uint256),bytes)[])", "incrementCounter()", "getCounter(address)", "getOrderHash((address,address,(uint8,address,uint256,uint256,uint256)[],(uint8,address,uint256,uint256,uint256,address)[],uint8,uint256,uint256,bytes32,uint256,bytes32,uint256))", "getOrderStatus(bytes32)", "information()", "getContractOffererNonce(address)", "fulfillBasicOrder_efficient_6GL6yc((address,uint256,uint256,address,address,address,uint256,uint256,uint8,uint256,uint256,bytes32,uint256,bytes32,bytes32,uint256,(uint256,address)[],bytes))",
    "getPrice()", "latestAnswer()", "latestRoundData()", "decimals()", "description()", "getRoundData(uint80)", "latestTimestamp()", "latestRound()", "aggregator()", "setFeeRecipient(address)", "feeRecipient()", "setFee(uint256)", "setTreasury(address)", "treasury()", "setRouter(address)", "router()", "setMaxTxAmount(uint256)", "setSwapAndLiquifyEnabled(bool)", "swapAndLiquifyEnabled()", "excludeFromFee(address)", "includeInFee(address)", "isExcludedFromFee(address)", "excludeFromReward(address)", "setTaxFeePercent(uint256)", "setLiquidityFeePercent(uint256)", "setMaxTxPercent(uint256)", "uniswapV2Pair()", "uniswapV2Router()", "openTrading()", "tradingOpen()", "setBots(address[])", "delBot(address)", "manualswap()", "manualsend()", "removeLimits()", "enableTrading()", "setMarketingWallet(address)", "marketingWallet()", "setDevWallet(address)", "devWallet()", "_maxTxAmount()", "_maxWalletSize()", "setMaxWalletSize(uint256)", "blacklistAddress(address,bool)", "isBot(address)", "antiBot()", "lockTheSwap()", "totalFees()", "deliver(uint256)", "reflectionFromToken(uint256,bool)", "tokenFromReflection(uint256)", "isExcludedFromReward(address)", "geUnlockTime()", "lock(uint256)", "unlock()",
    "nonces(uint256)", "tokenIdCounter()", "getApproved(uint256)", "burn(uint256)", "getRoleMember(bytes32,uint256)", "claimable(address)", "vestingSchedules(address)", "release()", "release(address)", "releasable()", "vestedAmount(uint64)", "start()", "duration()", "end()", "beneficiary()", "released()", "released(address)", "cliff()",
    "setApprovalForAll(address,bool)", "flashLoan(address,address,uint256,bytes)", "maxFlashLoan(address)", "flashFee(address,uint256)", "onFlashLoan(address,address,uint256,uint256,bytes)", "receiveFlashLoan(address[],uint256[],uint256[],bytes)",
    "createProxy(address,bytes)", "createClone(address)", "clone(address)", "cloneDeterministic(address,bytes32)", "predictDeterministicAddress(address,bytes32,address)", "deploy(bytes32,bytes)", "computeAddress(bytes32,bytes32)", "create2(bytes32,bytes)",
    "joinPool(uint256,uint256[])", "exitPool(uint256,uint256[])", "joinswapExternAmountIn(address,uint256,uint256)", "joinswapPoolAmountOut(address,uint256,uint256)", "exitswapPoolAmountIn(address,uint256,uint256)", "exitswapExternAmountOut(address,uint256,uint256)", "swapExactAmountIn(address,uint256,address,uint256,uint256)", "swapExactAmountOut(address,uint256,address,uint256,uint256)", "bind(address,uint256,uint256)", "rebind(address,uint256,uint256)", "unbind(address)", "finalize()", "gulp(address)", "setSwapFee(uint256)", "setController(address)", "setPublicSwap(bool)", "getSpotPrice(address,address)", "getSpotPriceSansFee(address,address)", "getBalance(address)", "getDenormalizedWeight(address)", "getNormalizedWeight(address)", "getTotalDenormalizedWeight()", "getController()", "getSwapFee()", "getNumTokens()", "getCurrentTokens()", "getFinalTokens()", "isBound(address)", "isFinalized()", "isPublicSwap()", "getColor()", "increaseApproval(address,uint256)", "decreaseApproval(address,uint256)",
    "calcSpotPrice(uint256,uint256,uint256,uint256,uint256)", "calcOutGivenIn(uint256,uint256,uint256,uint256,uint256,uint256)", "calcInGivenOut(uint256,uint256,uint256,uint256,uint256,uint256)", "calcPoolOutGivenSingleIn(uint256,uint256,uint256,uint256,uint256,uint256)", "calcSingleInGivenPoolOut(uint256,uint256,uint256,uint256,uint256,uint256)", "calcSingleOutGivenPoolIn(uint256,uint256,uint256,uint256,uint256,uint256)", "calcPoolInGivenSingleOut(uint256,uint256,uint256,uint256,uint256,uint256)",
    "BONE()", "BPOW_PRECISION()", "MIN_BOUND_TOKENS()", "MAX_BOUND_TOKENS()", "MIN_FEE()", "MAX_FEE()", "EXIT_FEE()", "MIN_WEIGHT()", "MAX_WEIGHT()", "MAX_TOTAL_WEIGHT()", "MIN_BALANCE()", "INIT_POOL_SUPPLY()", "MIN_BPOW_BASE()", "MAX_BPOW_BASE()", "MAX_IN_RATIO()", "MAX_OUT_RATIO()", "newBPool()", "isBPool(address)", "getBLabs()", "setBLabs(address)", "collect(address)",
    "m_numOwners()", "m_required()", "m_dailyLimit()", "m_spentToday()", "m_lastDay()", "confirm(bytes32)", "revoke(bytes32)", "changeOwner(address,address)", "changeRequirement(uint256)", "setDailyLimit(uint256)", "resetSpentToday()", "hasConfirmed(bytes32,address)", "kill(address)", "execute(address,uint256,bytes)", "isOwner(address)", "getOwner(uint256)", "getOwners()", "initMultiowned(address[],uint256)", "initDaylimit(uint256)", "initWallet(address[],uint256,uint256)", "_walletLibrary()",
    "fallback()", "receive()", "proxyOwner()", "transferProxyOwnership(address)", "upgradeTo(string,address)", "upgradeToAndCall(string,address,bytes)", "setImplementation(address)", "setPendingImplementation(address)", "acceptImplementation()", "_setImplementation(address,bool,bytes)", "comptrollerImplementation()", "pendingComptrollerImplementation()", "_become(address)",
];

pub const EVENTS: &[&str] = &[
    "Transfer(address,address,uint256)", "Approval(address,address,uint256)", "Transfer(address,address,uint256,bytes)", "TransferSingle(address,address,address,uint256,uint256)", "TransferBatch(address,address,address,uint256[],uint256[])", "ApprovalForAll(address,address,bool)", "URI(string,uint256)",
    "OwnershipTransferred(address,address)", "OwnershipTransferStarted(address,address)", "OwnerNominated(address)", "OwnerChanged(address,address)", "AdminChanged(address,address)", "Upgraded(address)", "BeaconUpgraded(address)", "Initialized(uint8)", "Initialized(uint64)",
    "Paused(address)", "Unpaused(address)", "Pause()", "Unpause()", "RoleGranted(bytes32,address,address)", "RoleRevoked(bytes32,address,address)", "RoleAdminChanged(bytes32,bytes32,bytes32)",
    "Deposit(address,uint256)", "Withdrawal(address,uint256)", "Deposit(address,address,uint256,uint256)", "Withdraw(address,address,address,uint256,uint256)", "Mint(address,uint256,uint256)", "Burn(address,uint256,uint256,address)", "Swap(address,uint256,uint256,uint256,uint256,address)", "Sync(uint112,uint112)", "PairCreated(address,address,address,uint256)",
    "Mint(address,address,int24,int24,uint128,uint256,uint256)", "Burn(address,int24,int24,uint128,uint256,uint256)", "Swap(address,address,int256,int256,uint160,uint128,int24)", "Collect(address,address,int24,int24,uint128,uint128)", "Flash(address,address,uint256,uint256,uint256,uint256)", "Initialize(uint160,int24)", "PoolCreated(address,address,uint24,int24,address)", "FeeAmountEnabled(uint24,int24)", "IncreaseObservationCardinalityNext(uint16,uint16)", "SetFeeProtocol(uint8,uint8,uint8,uint8)", "CollectProtocol(address,address,uint128,uint128)",
    "Issue(uint256)", "Redeem(uint256)", "Deprecate(address)", "Params(uint256,uint256)", "DestroyedBlackFunds(address,uint256)", "AddedBlackList(address)", "RemovedBlackList(address)", "Blacklisted(address)", "UnBlacklisted(address)", "BlacklisterChanged(address)", "PauserChanged(address)", "MasterMinterChanged(address)", "MinterConfigured(address,uint256)", "MinterRemoved(address)", "Mint(address,address,uint256)", "Burn(address,uint256)", "RescuerChanged(address)", "AuthorizationUsed(address,bytes32)", "AuthorizationCanceled(address,bytes32)",
    "ExecutionSuccess(bytes32,uint256)", "ExecutionFailure(bytes32,uint256)", "AddedOwner(address)", "RemovedOwner(address)", "ChangedThreshold(uint256)", "EnabledModule(address)", "DisabledModule(address)", "ExecutionFromModuleSuccess(address)", "ExecutionFromModuleFailure(address)", "SafeSetup(address,address[],uint256,address,address)", "ApproveHash(bytes32,address)", "SignMsg(bytes32)", "ChangedFallbackHandler(address)", "ChangedGuard(address)", "SafeReceived(address,uint256)", "ProxyCreation(address,address)", "SafeMultiSigTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes,bytes)", "SafeModuleTransaction(address,address,uint256,bytes,uint8)",
    "Mint(address,uint256,uint256)", "Redeem(address,uint256,uint256)", "Borrow(address,uint256,uint256,uint256)", "RepayBorrow(address,address,uint256,uint256,uint256)", "LiquidateBorrow(address,address,uint256,address,uint256)", "AccrueInterest(uint256,uint256,uint256,uint256)", "NewPendingAdmin(address,address)", "NewAdmin(address,address)", "NewComptroller(address,address)", "NewMarketInterestRateModel(address,address)", "NewReserveFactor(uint256,uint256)", "ReservesAdded(address,uint256,uint256)", "ReservesReduced(address,uint256,uint256)", "Failure(uint256,uint256,uint256)", "MarketEntered(address,address)", "MarketExited(address,address)",
    "NewOwner(bytes32,bytes32,address)", "Transfer(bytes32,address)", "NewResolver(bytes32,address)", "NewTTL(bytes32,uint64)", "AddrChanged(bytes32,address)", "NameChanged(bytes32,string)", "NameRegistered(string,bytes32,address,uint256,uint256)", "NameRenewed(string,bytes32,uint256,uint256)",
    "Supply(address,address,address,uint256,uint16)", "Withdraw(address,address,address,uint256)", "Borrow(address,address,address,uint256,uint8,uint256,uint16)", "Repay(address,address,address,uint256,bool)", "FlashLoan(address,address,address,uint256,uint8,uint256,uint16)", "LiquidationCall(address,address,address,uint256,uint256,address,bool)", "ReserveUsedAsCollateralEnabled(address,address)", "ReserveUsedAsCollateralDisabled(address,address)", "ReserveDataUpdated(address,uint256,uint256,uint256,uint256,uint256)",
    "TokenExchange(address,int128,uint256,int128,uint256)", "TokenExchange(address,uint256,uint256,uint256,uint256)", "TokenExchange(address,uint256,uint256,uint256,uint256,uint256,uint256)", "TokenExchangeUnderlying(address,int128,uint256,int128,uint256)", "AddLiquidity(address,uint256[3],uint256[3],uint256,uint256)", "AddLiquidity(address,uint256[2],uint256[2],uint256,uint256)", "AddLiquidity(address,uint256[3],uint256,uint256,uint256,uint256)", "RemoveLiquidity(address,uint256[3],uint256[3],uint256)", "RemoveLiquidity(address,uint256[2],uint256[2],uint256)", "RemoveLiquidity(address,uint256[3],uint256)", "RemoveLiquidityOne(address,uint256,uint256)", "RemoveLiquidityOne(address,uint256,uint256,uint256,uint256)", "RemoveLiquidityImbalance(address,uint256[3],uint256[3],uint256,uint256)", "CommitNewAdmin(uint256,address)", "NewAdmin(address)", "CommitNewFee(uint256,uint256,uint256)", "CommitNewParameters(uint256,uint256,uint256,uint256,uint256,uint256)", "NewFee(uint256,uint256)", "NewParameters(uint256,uint256,uint256,uint256,uint256)", "RampA(uint256,uint256,uint256,uint256)", "StopRampA(uint256,uint256)", "RampAgamma(uint256,uint256,uint256,uint256,uint256,uint256)", "StopRampA(uint256,uint256,uint256)", "ClaimAdminFee(address,uint256)",
    "OrderFilled(address,bytes32,uint256)", "OrderCanceled(address,bytes32,uint256)", "OrderFilledRFQ(bytes32,uint256)", "NonceIncreased(address,uint256)", "Swapped(address,address,address,address,uint256,uint256)",
    "OrderFulfilled(bytes32,address,address,address,(uint8,address,uint256,uint256)[],(uint8,address,uint256,uint256,address)[])", "OrderCancelled(bytes32,address,address)", "OrderValidated(bytes32,(address,address,(uint8,address,uint256,uint256,uint256)[],(uint8,address,uint256,uint256,uint256,address)[],uint8,uint256,uint256,bytes32,uint256,bytes32,uint256))", "OrdersMatched(bytes32[])", "CounterIncremented(uint256,address)",
    "DelegateChanged(address,address,address)", "DelegateVotesChanged(address,uint256,uint256)", "MinterChanged(address,address)", "ProposalCreated(uint256,address,address[],uint256[],string[],bytes[],uint256,uint256,string)", "VoteCast(address,uint256,bool,uint256)", "VoteCast(address,uint256,uint8,uint256,string)", "ProposalCanceled(uint256)", "ProposalQueued(uint256,uint256)", "ProposalExecuted(uint256)", "QueueTransaction(bytes32,address,uint256,string,bytes,uint256)", "ExecuteTransaction(bytes32,address,uint256,string,bytes,uint256)", "CancelTransaction(bytes32,address,uint256,string,bytes,uint256)", "NewDelay(uint256)",
    "Submitted(address,uint256,address)", "Staked(address,uint256)", "Withdrawn(address,uint256)", "RewardPaid(address,uint256)", "RewardAdded(uint256)", "Claimed(address,uint256)", "TokensReleased(address,uint256)", "EtherReleased(uint256)", "ERC20Released(address,uint256)", "ProxyCreated(address)", "ContractCreated(address)", "Received(address,uint256)", "Executed(address,uint256,bytes)", "CallExecuted(bytes32,uint256,address,uint256,bytes)", "Permit(address,address,address,uint160,uint48,uint48)", "NonceInvalidation(address,address,address,uint48,uint48)", "UnorderedNonceInvalidation(address,uint256,uint256)", "Lockdown(address,address,address)", "Approval(address,address,address,uint160,uint48)",
    "LOG_SWAP(address,address,address,uint256,uint256)", "LOG_JOIN(address,address,uint256)", "LOG_EXIT(address,address,uint256)", "LOG_NEW_POOL(address,address)", "LOG_BLABS(address,address)",
    "Confirmation(address,bytes32)", "Revoke(address,bytes32)", "OwnerAdded(address)", "OwnerRemoved(address)", "RequirementChanged(uint256)", "SingleTransact(address,uint256,address,bytes)", "MultiTransact(address,bytes32,uint256,address,bytes)", "ConfirmationNeeded(bytes32,address,uint256,address,bytes)", "SingleTransact(address,uint256,address,bytes,address)", "MultiTransact(address,bytes32,uint256,address,bytes,address)",
    "LogNote(bytes4,address,bytes32,bytes32,bytes)", "LogSetAuthority(address)", "LogSetOwner(address)", "Rely(address)", "Deny(address)", "File(bytes32,uint256)", "File(bytes32,address)", "Cage()", "Poke(bytes32,bytes32,uint256)", "Drip(bytes32)", "Join(address,uint256)", "Exit(address,uint256)",
    "AnswerUpdated(int256,uint256,uint256)", "NewRound(uint256,address,uint256)", "SwapAndLiquify(uint256,uint256,uint256)", "MinTokensBeforeSwapUpdated(uint256)", "SwapAndLiquifyEnabledUpdated(bool)", "MaxTxAmountUpdated(uint256)", "ExcludeFromFee(address)", "Snapshot(uint256)", "Mint(address,uint256)", "Burned(address,uint256)", "Minted(address,uint256)", "TokensMinted(address,uint256)", "TokensBurned(address,uint256)", "Locked(address,uint256)", "Unlocked(address,uint256)", "Stake(address,uint256)", "Unstake(address,uint256)", "Harvest(address,uint256)", "EmergencyWithdraw(address,uint256,uint256)", "Deposit(address,uint256,uint256)", "Withdraw(address,uint256,uint256)", "ImplementationUpdated(address,address)", "ProxyOwnershipTransferred(address,address)", "ProxyUpdated(address,address)", "NewImplementation(address,address)", "NewPendingImplementation(address,address)",
];

pub const ERRORS: &[&str] = &[
    "Error(string)",
    "Panic(uint256)",
    "OwnableUnauthorizedAccount(address)",
    "OwnableInvalidOwner(address)",
    "AccessControlUnauthorizedAccount(address,bytes32)",
    "AccessControlBadConfirmation()",
    "EnforcedPause()",
    "ExpectedPause()",
    "ReentrancyGuardReentrantCall()",
    "ERC20InsufficientBalance(address,uint256,uint256)",
    "ERC20InvalidSender(address)",
    "ERC20InvalidReceiver(address)",
    "ERC20InsufficientAllowance(address,uint256,uint256)",
    "ERC20InvalidApprover(address)",
    "ERC20InvalidSpender(address)",
    "ERC721InvalidOwner(address)",
    "ERC721NonexistentToken(uint256)",
    "ERC721IncorrectOwner(address,uint256,address)",
    "ERC721InvalidSender(address)",
    "ERC721InvalidReceiver(address)",
    "ERC721InsufficientApproval(address,uint256)",
    "ERC721InvalidApprover(address)",
    "ERC721InvalidOperator(address)",
    "ERC1155InsufficientBalance(address,uint256,uint256,uint256)",
    "ERC1155InvalidSender(address)",
    "ERC1155InvalidReceiver(address)",
    "ERC1155MissingApprovalForAll(address,address)",
    "ERC1155InvalidApprover(address)",
    "ERC1155InvalidOperator(address)",
    "ERC1155InvalidArrayLength(uint256,uint256)",
    "ERC2612ExpiredSignature(uint256)",
    "ERC2612InvalidSigner(address,address)",
    "InvalidAccountNonce(address,uint256)",
    "ECDSAInvalidSignature()",
    "ECDSAInvalidSignatureLength(uint256)",
    "ECDSAInvalidSignatureS(bytes32)",
    "SafeERC20FailedOperation(address)",
    "FailedInnerCall()",
    "AddressInsufficientBalance(address)",
    "AddressEmptyCode(address)",
    "FailedCall()",
    "InsufficientBalance(uint256,uint256)",
    "FailedDeployment()",
    "ERC1967InvalidImplementation(address)",
    "ERC1967InvalidAdmin(address)",
    "ERC1967InvalidBeacon(address)",
    "ERC1967NonPayable()",
    "UUPSUnauthorizedCallContext()",
    "UUPSUnsupportedProxiableUUID(bytes32)",
    "InvalidInitialization()",
    "NotInitializing()",
    "ProxyDeniedAdminAccess()",
    "AllowanceExpired(uint256)",
    "InsufficientAllowance(uint256)",
    "ExcessiveInvalidation()",
    "InvalidAmount(uint256)",
    "LengthMismatch()",
    "InvalidNonce()",
    "SignatureExpired(uint256)",
    "InvalidSignature()",
    "InvalidSignatureLength()",
    "InvalidSigner()",
    "InvalidContractSignature()",
    "InvalidSpender()",
    "TransactionDeadlinePassed()",
    "V2TooLittleReceived()",
    "V2TooMuchRequested()",
    "V2InvalidPath()",
    "V3TooLittleReceived()",
    "V3TooMuchRequested()",
    "V3InvalidSwap()",
    "V3InvalidCaller()",
    "V3InvalidAmountOut()",
    "ExecutionFailed(uint256,bytes)",
    "ETHNotAccepted()",
    "InvalidCommandType(uint256)",
    "InsufficientToken()",
    "InsufficientETH()",
    "FromAddressIsNotOwner()",
    "InvalidBips()",
    "UnsafeCast()",
    "ContractLocked()",
    "InvalidReserves()",
    "InvalidPath()",
    "InvalidTime()",
    "InvalidMsgValue()",
    "BadFulfillmentComponents()",
    "OrderAlreadyFilled(bytes32)",
    "InvalidSigner()",
    "InvalidCanceller()",
    "BadSignatureV(uint8)",
    "InvalidSignature()",
    "InvalidTime(uint256,uint256)",
    "OrderIsCancelled(bytes32)",
    "OrderPartiallyFilled(bytes32)",
    "ConsiderationNotMet(uint256,uint256,uint256)",
    "InsufficientNativeTokensSupplied()",
    "NativeTokenTransferGenericFailure(address,uint256)",
    "InvalidERC721TransferAmount(uint256)",
    "InvalidContractOrder(bytes32)",
    "NoReentrantCalls()",
    "InvalidCallToConduit(address)",
    "MissingItemAmount()",
    "UnusedItemParameters()",
    "InvalidBasicOrderParameterEncoding()",
    "OrderCriteriaResolverOutOfRange(uint8)",
    "CriteriaNotEnabledForItem()",
    "InvalidProof()",
    "InvalidRestrictedOrder(bytes32)",
    "Invalid1155BatchTransferEncoding()",
    "NoSpecifiedOrdersAvailable()",
    "InvalidNativeOfferItem()",
    "PartialFillsNotEnabledForOrder()",
    "InvalidFulfillmentComponentData()",
    "InexactFraction()",
    "MismatchedFulfillmentOfferAndConsiderationComponents(uint256)",
    "OfferAndConsiderationRequiredOnFulfillment()",
    "InvalidMsgValue(uint256)",
    "BadReturnValueFromERC20OnTransfer(address,address,address,uint256)",
    "TokenTransferGenericFailure(address,address,address,uint256,uint256)",
    "NoContract(address)",
    "BadContractSignature()",
    "ZeroAddress()",
    "ZeroAmount()",
    "Unauthorized()",
    "NotOwner()",
    "NotAdmin()",
    "Forbidden()",
    "InvalidAddress()",
    "InvalidInput()",
    "InvalidParameter()",
    "InsufficientFunds()",
    "InsufficientBalance()",
    "InsufficientLiquidity()",
    "Expired()",
    "Deadline()",
    "DeadlineExpired()",
    "Slippage()",
    "Reentrancy()",
    "Reentrant()",
    "AlreadyInitialized()",
    "NotInitialized()",
    "Paused()",
    "NotPaused()",
    "Locked()",
    "TransferFailed()",
    "ETHTransferFailed()",
    "ApproveFailed()",
    "CallFailed()",
    "InvalidSelector()",
    "InvalidLength()",
    "ArrayLengthMismatch()",
    "AmountTooLow()",
    "AmountTooHigh()",
    "ExceedsMaxSupply()",
    "MaxSupplyReached()",
    "SoldOut()",
    "SaleNotActive()",
    "MintingNotActive()",
    "InvalidProof()",
    "AlreadyClaimed()",
    "NotWhitelisted()",
    "NothingToClaim()",
    "InvalidPrice()",
    "InvalidToken()",
    "InvalidRecipient()",
    "InvalidCaller()",
    "OnlyOwner()",
    "OnlyAdmin()",
    "OnlyPool()",
    "OnlyFactory()",
    "OnlyRouter()",
    "NotAuthorized()",
    "CallerNotOwner()",
    "InvalidImplementation()",
    "SameAddress()",
    "AlreadyExists()",
    "DoesNotExist()",
    "NotFound()",
    "OutOfBounds()",
    "IndexOutOfBounds()",
    "Overflow()",
    "Underflow()",
    "DivisionByZero()",
    "MathOverflowedMulDiv()",
    "StringsInsufficientHexLength(uint256,uint256)",
    "StringsInvalidChar()",
    "SafeCastOverflowedUintDowncast(uint8,uint256)",
    "SafeCastOverflowedIntToUint(int256)",
    "SafeCastOverflowedUintToInt(uint256)",
    "CheckpointUnorderedInsertion()",
    "ERC20ExceededCap(uint256,uint256)",
    "ERC20InvalidCap(uint256)",
    "ERC4626ExceededMaxDeposit(address,uint256,uint256)",
    "ERC4626ExceededMaxMint(address,uint256,uint256)",
    "ERC4626ExceededMaxWithdraw(address,uint256,uint256)",
    "ERC4626ExceededMaxRedeem(address,uint256,uint256)",
    "VotesExpiredSignature(uint256)",
    "GovernorInvalidProposalLength(uint256,uint256,uint256)",
    "GovernorAlreadyCastVote(address)",
    "GovernorDisabledDeposit()",
    "GovernorOnlyExecutor(address)",
    "GovernorNonexistentProposal(uint256)",
    "GovernorUnexpectedProposalState(uint256,uint8,bytes32)",
    "GovernorInvalidVotingPeriod(uint256)",
    "GovernorInsufficientProposerVotes(address,uint256,uint256)",
    "GovernorRestrictedProposer(address)",
    "GovernorInvalidVoteType()",
    "GovernorQueueNotImplemented()",
    "GovernorNotQueuedProposal(uint256)",
    "GovernorAlreadyQueuedProposal(uint256)",
    "GovernorInvalidSignature(address)",
    "TimelockUnexpectedOperationState(bytes32,bytes32)",
    "TimelockUnexecutedPredecessor(bytes32)",
    "TimelockInvalidOperationLength(uint256,uint256,uint256)",
    "TimelockInsufficientDelay(uint256,uint256)",
    "TimelockUnauthorizedCaller(address)",
    "Create2EmptyBytecode()",
    "Create2FailedDeployment()",
    "Create2InsufficientBalance(uint256,uint256)",
    "ERC1167FailedCreateClone()",
    "MulticallFailed()",
    "SafeERC20FailedDecreaseAllowance(address,uint256,uint256)",
    "InvalidShortString()",
    "StringTooLong(string)",
    "ERC2981InvalidDefaultRoyalty(uint256,uint256)",
    "ERC2981InvalidDefaultRoyaltyReceiver(address)",
    "ERC2981InvalidTokenRoyalty(uint256,uint256,uint256)",
    "ERC2981InvalidTokenRoyaltyReceiver(uint256,address)",
    "ERC721EnumerableForbiddenBatchMint()",
    "ERC721OutOfBoundsIndex(address,uint256)",
    "ERC2771InvalidForwarder(address)",
];
