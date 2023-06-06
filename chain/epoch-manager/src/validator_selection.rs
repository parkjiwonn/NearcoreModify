use crate::shard_assignment::assign_shards;
use near_primitives::checked_feature;
use near_primitives::epoch_manager::epoch_info::EpochInfo;
use near_primitives::epoch_manager::{EpochConfig, RngSeed};
use near_primitives::errors::EpochError;
use near_primitives::types::validator_stake::ValidatorStake;
use near_primitives::types::{
    AccountId, Balance, ProtocolVersion, ValidatorId, ValidatorKickoutReason,
};
use num_rational::Ratio;
use std::cmp::{self, Ordering};
use std::collections::hash_map;
use std::collections::{BTreeMap, BinaryHeap, HashMap, HashSet};
use tracing::log::log;

/// Select validators for next epoch and generate epoch info
/// 다음 에포크의 유효성 검사기를 선택하고 에포크 정보를 생성한다.
pub fn proposals_to_epoch_info(
    epoch_config: &EpochConfig,
    rng_seed: RngSeed,
    prev_epoch_info: &EpochInfo,
    proposals: Vec<ValidatorStake>,
    mut validator_kickout: HashMap<AccountId, ValidatorKickoutReason>,
    validator_reward: HashMap<AccountId, Balance>,/// 의문 -> 이 balance가 스테이킹한 돈인지 아니면 그냥 계정의 잔액 인건지 모르겠음.
    minted_amount: Balance,
    next_version: ProtocolVersion,
    last_version: ProtocolVersion,
) -> Result<EpochInfo, EpochError> {
    debug_assert!(
        /// proposal 백터에 중복되는 제안이 있는지 먼저 확인한다.
        proposals.iter().map(|stake| stake.account_id()).collect::<HashSet<_>>().len()
            == proposals.len(),
        "Proposals should not have duplicates"
        //" 제안서에는 중복된 내용이 없어야 합니다."
    );

    let num_shards = epoch_config.shard_layout.num_shards();
    let min_stake_ratio = {
        let rational = epoch_config.validator_selection_config.minimum_stake_ratio;
        Ratio::new(*rational.numer() as u128, *rational.denom() as u128)
    };
    let max_bp_selected = epoch_config.num_block_producer_seats as usize;
    /// 현재 epoch의 구성 정보인 epoch_config에서 필요한 값들을 추출한다.
    /// 좌석 배정에 필요한 최소 스케이크 비율, 최대 블록 생산자 좌석 수 등이다.
    ///
    /// stake 변경?
    let mut stake_change = BTreeMap::new();
    /// fisherman 정보를 기록하는 부분, fisherman 백터를 생성한다.
    let mut fishermen = vec![];
    /// proposals_with_rollover 함수 호출해서 제안들 처리하고 stake_change, fisherman 정보를 기록한다.
    let proposals = proposals_with_rollover(
        proposals,
        prev_epoch_info,
        &validator_reward,
        &validator_kickout,
        &mut stake_change,
        &mut fishermen,
    );
    /// 블록 생산자 제안 -> 제안 정렬한다.
    let mut block_producer_proposals = order_proposals(proposals.values().cloned());
    /// 블록 생산자 선택하고 선택된 블록 생산자와 스테이크 임계값을 반환한다.
    let (block_producers, bp_stake_threshold) = select_block_producers(
        &mut block_producer_proposals, /// 블록 생산자 제안들
        max_bp_selected, /// 선택된 블록 생산자
        min_stake_ratio, /// 스테이크 임계값
        last_version,
    );
    let (chunk_producer_proposals, chunk_producers, cp_stake_threshold) =
        if checked_feature!("stable", ChunkOnlyProducers, next_version) {
            let mut chunk_producer_proposals = order_proposals(proposals.into_values());
            let max_cp_selected = max_bp_selected
                + (epoch_config.validator_selection_config.num_chunk_only_producer_seats as usize);
            let (chunk_producers, cp_stake_treshold) = select_chunk_producers(
                &mut chunk_producer_proposals,
                max_cp_selected,
                min_stake_ratio,
                num_shards,
                last_version,
            );
            (chunk_producer_proposals, chunk_producers, cp_stake_treshold)
        } else {
            (block_producer_proposals, block_producers.clone(), bp_stake_threshold)
        };

    // since block producer proposals could become chunk producers, their actual stake threshold
    // is the smaller of the two thresholds
    // 블록 생산자 제인이 청크 생산자가 될 수 있으므로 실제 지분 임계값은 두 임계값 중 더 작은 임계값이다.
    let threshold = cmp::min(bp_stake_threshold, cp_stake_threshold);

    // process remaining chunk_producer_proposals that were not selected for either role
    // 어느 역활에도 선택되지 않은 나머지 청크 생산자 제안을 처리하는 것.
    for OrderedValidatorStake(p) in chunk_producer_proposals {
        let stake = p.stake();
        let account_id = p.account_id();
        if stake >= epoch_config.fishermen_threshold {
            fishermen.push(p);
        } else {
            *stake_change.get_mut(account_id).unwrap() = 0;
            if prev_epoch_info.account_is_validator(account_id)
                || prev_epoch_info.account_is_fisherman(account_id)
            {
                debug_assert!(stake < threshold);
                let account_id = p.take_account_id();
                validator_kickout.insert(
                    account_id,
                    ValidatorKickoutReason::NotEnoughStake { stake, threshold },
                );
            }
        }
    }

    // 청크 생산자 수
    let num_chunk_producers = chunk_producers.len();
    let mut all_validators: Vec<ValidatorStake> = Vec::with_capacity(num_chunk_producers);
    let mut validator_to_index = HashMap::new();
    let mut block_producers_settlement = Vec::with_capacity(block_producers.len());

    for (i, bp) in block_producers.into_iter().enumerate() {
        let id = i as ValidatorId;
        validator_to_index.insert(bp.account_id().clone(), id);
        block_producers_settlement.push(id);
        all_validators.push(bp);
    }

    let chunk_producers_settlement = if checked_feature!("stable", ChunkOnlyProducers, next_version)
    {
        let minimum_validators_per_shard =
            epoch_config.validator_selection_config.minimum_validators_per_shard as usize;
        let shard_assignment =
            assign_shards(chunk_producers, num_shards, minimum_validators_per_shard).map_err(
                |_| EpochError::NotEnoughValidators {
                    num_validators: num_chunk_producers as u64,
                    num_shards,
                },
            )?;

        let mut chunk_producers_settlement: Vec<Vec<ValidatorId>> =
            shard_assignment.iter().map(|vs| Vec::with_capacity(vs.len())).collect();
        let mut i = all_validators.len();
        // Here we assign validator ids to all chunk only validators
        for (shard_validators, shard_validator_ids) in
            shard_assignment.into_iter().zip(chunk_producers_settlement.iter_mut())
        {
            for validator in shard_validators {
                debug_assert_eq!(i, all_validators.len());
                match validator_to_index.entry(validator.account_id().clone()) {
                    hash_map::Entry::Vacant(entry) => {
                        let validator_id = i as ValidatorId;
                        entry.insert(validator_id);
                        shard_validator_ids.push(validator_id);
                        all_validators.push(validator);
                        i += 1;
                    }
                    // Validators which have an entry in the validator_to_index map
                    // have already been inserted into `all_validators`.
                    hash_map::Entry::Occupied(entry) => {
                        let validator_id = *entry.get();
                        shard_validator_ids.push(validator_id);
                    }
                }
            }
        }
        chunk_producers_settlement
    } else {
        if chunk_producers.is_empty() {
            // All validators tried to unstake?
            return Err(EpochError::NotEnoughValidators { num_validators: 0u64, num_shards });
        }
        let mut id = 0usize;
        // Here we assign validators to chunks (we try to keep number of shards assigned for
        // each validator as even as possible). Note that in prod configuration number of seats
        // per shard is the same as maximal number of block producers, so normally all
        // validators would be assigned to all chunks
        (0usize..(num_shards as usize))
            .map(|shard_id| {
                (0..epoch_config.num_block_producer_seats_per_shard[shard_id]
                    .min(block_producers_settlement.len() as u64))
                    .map(|_| {
                        let res = block_producers_settlement[id];
                        id = (id + 1) % block_producers_settlement.len();
                        res
                    })
                    .collect()
            })
            .collect()
    };

    let fishermen_to_index = fishermen
        .iter()
        .enumerate()
        .map(|(index, s)| (s.account_id().clone(), index as ValidatorId))
        .collect::<HashMap<_, _>>();

    Ok(EpochInfo::new(
        prev_epoch_info.epoch_height() + 1,
        all_validators,
        validator_to_index,
        block_producers_settlement,
        chunk_producers_settlement,
        vec![],
        fishermen,
        fishermen_to_index,
        stake_change,
        validator_reward,
        validator_kickout,
        minted_amount,
        threshold,
        next_version,
        rng_seed,
    ))
} /// proposals_to_epoch_info 까지

/// Generates proposals based on new proposals, last epoch validators/fishermen and validator
/// kickouts
/// 새로운 제안들, 지난 에포크 검증자 / fisherman 및 검증자 킥아웃을 기반으로 제안이 생성된다.
/// For each account that was validator or fisherman in last epoch or made stake action last epoch
/// we apply the following in the order of priority
/// 지난 에포크에서 검증인 또는 fisherman였거나 지난 에포크에서 스테이크 액션을 수행한 각 계정에 대해 우선순위에 따라 다음을 적용한다.
/// 1. If account is in validator_kickout it cannot be validator or fisherman for the next epoch,
///        we will not include it in proposals or fishermen
/// 1. 계정이 검증인 킥아웃 상태인 경우 다음 에포크의 검증인 또는 fisherman이 될 수 없다.
/// 2. If account made staking action last epoch, it will be included in proposals with stake
///        adjusted by rewards from last epoch, if any
/// 2. 계정이 지난 에포크에서 스테이킹 한 경우, 지난 에포크의 보상으로 조정된 스테이킁으로 제안서에 포함된다.
/// 3. If account was validator last epoch, it will be included in proposals with the same stake
///        as last epoch, adjusted by rewards from last epoch, if any
/// 3. 계정이 지난 에포크에서 검증자였던 경우, 지난 에포크와 동일한 지분으로 제안서에 포함된다.
/// 4. If account was fisherman last epoch, it is included in fishermen
fn proposals_with_rollover(
    proposals: Vec<ValidatorStake>,
    prev_epoch_info: &EpochInfo,
    validator_reward: &HashMap<AccountId, Balance>,
    validator_kickout: &HashMap<AccountId, ValidatorKickoutReason>,
    stake_change: &mut BTreeMap<AccountId, Balance>,
    fishermen: &mut Vec<ValidatorStake>,
) -> HashMap<AccountId, ValidatorStake> {

    let mut proposals_by_account = HashMap::new();

    for p in proposals {
        let account_id = p.account_id();
        if validator_kickout.contains_key(account_id) {
            let account_id = p.take_account_id();
            stake_change.insert(account_id, 0);
        } else {
            stake_change.insert(account_id.clone(), p.stake());
            proposals_by_account.insert(account_id.clone(), p);
        }
    }

    for r in prev_epoch_info.validators_iter() {
        let account_id = r.account_id().clone();
        if validator_kickout.contains_key(&account_id) {
            stake_change.insert(account_id, 0);
            continue;
        }
        let p = proposals_by_account.entry(account_id).or_insert(r);
        if let Some(reward) = validator_reward.get(p.account_id()) {
            *p.stake_mut() += *reward;
        }
        stake_change.insert(p.account_id().clone(), p.stake());
    }

    for r in prev_epoch_info.fishermen_iter() {
        let account_id = r.account_id();
        if validator_kickout.contains_key(account_id) {
            stake_change.insert(account_id.clone(), 0);
            continue;
        }
        if !proposals_by_account.contains_key(account_id) {
            // safe to do this here because fishermen from previous epoch is guaranteed to have no
            // duplicates.
            stake_change.insert(account_id.clone(), r.stake());
            fishermen.push(r);
        }
    }

    proposals_by_account
}

fn order_proposals<I: IntoIterator<Item = ValidatorStake>>(
    proposals: I,
) -> BinaryHeap<OrderedValidatorStake> {
    proposals.into_iter().map(OrderedValidatorStake).collect()
}

// ======================블록 생산자 선택
fn select_block_producers(
    block_producer_proposals: &mut BinaryHeap<OrderedValidatorStake>,
    max_num_selected: usize,
    min_stake_ratio: Ratio<u128>,
    protocol_version: ProtocolVersion,
) -> (Vec<ValidatorStake>, Balance) {
    select_validators(block_producer_proposals, max_num_selected, min_stake_ratio, protocol_version)
}
// ======================블록 생산자 선택
fn select_chunk_producers(
    all_proposals: &mut BinaryHeap<OrderedValidatorStake>,
    max_num_selected: usize,
    min_stake_ratio: Ratio<u128>,
    num_shards: u64,
    protocol_version: ProtocolVersion,
) -> (Vec<ValidatorStake>, Balance) {
    select_validators(
        all_proposals,
        max_num_selected,
        min_stake_ratio * Ratio::new(1, num_shards as u128),
        protocol_version,
    )
}

// Takes the top N proposals (by stake), or fewer if there are not enough or the
// next proposals is too small relative to the others. In the case where all N
// slots are filled, or the stake ratio falls too low, the threshold stake to be included
// is also returned.
// 스테이크 별로 상위 N개의 제안을 받거나, 제안이 충분하지 않거나 다음 제안이 다른 제안에 비해 너무 작으면 그보다 적은 수의 제안을 받는다.
// 예를들어 N = 10인데
// N 슬롯이 모두 채워지거나 지분 비율이 너무 낮을 경우, 포함할 임계 지분도 반환된다.
// ============================ 여기서 검증자가 선출되는 것 같다. ============================
fn select_validators(
    proposals: &mut BinaryHeap<OrderedValidatorStake>,
    max_number_selected: usize, // 선택된 수
    min_stake_ratio: Ratio<u128>, // 스테이킹한 최소 비율?
    protocol_version: ProtocolVersion,
) -> (Vec<ValidatorStake>, Balance) {
    let mut total_stake = 0; // 총 스테이킹
    // 여기서 n이 상위 N 말하는 것 같다.
    let n = cmp::min(max_number_selected, proposals.len());
    // max_number_selected 와 proposal.len() 중 작은값을 n으로 설정한다.
    // 최대 선택 수와 제출된 제안서 중에서 작은 값을 선택하는 것을 의미한다.
    // Q.근데 왜 최대 선택 수와 제출된 제안서 중에서 작은 값을 선택하는 걸까 ?
    let mut validators = Vec::with_capacity(n);
    // 용량을 n으로 설정한다. Vec는 선택된 검증자를 저장하나?
    // 검증자를 n명 수용할 수 있는 validators

    // 최종적으로는 n명을 뽑지만 원래 tpos대로 반만 뽑는다.
    let half_n = n / 2;
    ///======================Validator 뽑는 for 문========================
    for _ in 0..half_n {
        // n번 반복하는 반복문
        // 상위 N개의 제안서를 선택하는 과정을 나타냄.
        // 제안자들 리스트에서 가장 위에 있는 애
        let p = proposals.pop().unwrap().0;
        // proposals에서 0번째 가장 큰값을 꺼낸다. p 에 할당한다. OrderedValidatorStake가 스테이크를 최대힙에 저장하고 가장 큰 상태와 사전적으로 가장 작은 상태 순으로 정렬했으니까.
        let p_stake = p.stake();
        // p의 stake값을 할당한다.
        let total_stake_with_p = total_stake + p_stake;
        // for 문 돌면서 제일 높은 stake를 지불한 사람의 stake를 더한다.

        // Ratio -> 분수 만드는 라이브러리
        // numer : 분자 , demon : 분모 -> 새로운 Ratio 객체 생성한다.
        // 현재 뽑힌 제안자의 stake와 총 스테이킹 비율을 분수로 만든다. 그게 최소 비율 보다 큰지 확인한다.
        // t
        if Ratio::new(p_stake, total_stake_with_p) > min_stake_ratio {
            // 현재 제안서의 stake 비율이 최소 stake(min_stake_ratio) 비율 보다 큰지 확인한다.
            validators.push(p);

            // 비율보다 크다면 해당 제안서를 선택해 validator 벡터에 추가한다.
            total_stake = total_stake_with_p;
            // 현재까지의 총 스테이킹 값을 갱신하는 것을 의미함.
        } else {
            // p was not included, return it to the list of proposals
            // p 가 포함되지 않은 경우, 제안의 목록들로 반환된다.
            ///==================탈락한 제안자들 list=================
            proposals.push(OrderedValidatorStake(p));
            // 그럼 여기서 proposals에 반환된 애들은 탈락된 얘들만 모이겠네?
            break;
        }
    }
    ///======================Validator 뽑는 for 문========================

    ///======================나머지 뽑는 for 문========================
    log!("탈락한 제안자들 list : " + proposals);
    /// tpos 방식으로 뽑힌 검증자들 빼고 나머지 인원수 만큼 뽑아야 하니까.
    let left = n-validators.len();
    /// 탈락한 제안자들의 소득 분위를 나눠야 하는데 어떻게 나눠 염병 시발
    /// for문을 돌려 - 탈락한 사람들 수 만큼
    for _ in 0..left{

        // 남은 사람들이 스테이킹한 금액을 살펴 봐야 하는데


    }


    // 나머지 애들을 뽑는 for 돌려야겠음.

    // 선택된 검증자의 수가 최대 선택 수와 같은지 확인한다. => 모든 슬롯이 채워졌는지 확인
    if validators.len() == max_number_selected {
        // all slots were filled, so the threshold stake is 1 more than the current
        // smallest stake
        // 모든 슬롯이 채워졌으므로 임계값 지분은 현재 가장 작은 지분보다 1 더 많다.
        let threshold = validators.last().unwrap().stake() + 1;
        // 이미 모든 슬롯이 채워졌으니 추가적인 슬롯을 채우기 위한 임계값으로 가장 작은 지분보다 1더 큰 값이 사용된다.

        (validators, threshold)
        // 선택된 검증자와 임계값을 반환한다.
    } else {
        // the stake ratio condition prevented all slots from being filled,
        // or there were fewer proposals than available slots,
        // so the threshold stake is whatever amount pass the stake ratio condition
        // 지분 비율 조건으로 인해 모든 슬롯이 채워지지 않는다.
        // 또는 사용 가능한 슬롯보다 제안 수가 적었다.
        // 따라서 임계 지분은 지분 비율 조건을 통과하는 금액이다.

        // threshold는 지분 비율 조건을 충족하는 지분의 금액을 나타낸다.
        let threshold = if checked_feature!(
            "protocol_feature_fix_staking_threshold",
            // 스테이킹 임계값을 fix 한다.
            FixStakingThreshold,
            protocol_version
            // 스테이킹 임계값을 수정하는 기능이 활성화 되어있는지 확인함.
        ) {
            // 해당 기능이 활성화 되어있다면.
            (min_stake_ratio * Ratio::from_integer(total_stake)
                / (Ratio::from_integer(1u128) - min_stake_ratio))
                .ceil()
                .to_integer()// 소수점으로 올림하고 정수로 변화한것. -> 임계값을 정수형태로 얻기위함.
        } else { // 만약 기능이 비활성화 되어있다면
            (min_stake_ratio * Ratio::new(total_stake, 1)).ceil().to_integer()
        };
        (validators, threshold)
    }
}

/// We store stakes in max heap and want to order them such that the validator
/// with the largest state and (in case of a tie) lexicographically smallest
/// AccountId comes at the top.
/// 스테이크를 최대힙에 저장하고 가장 큰 상태와 사전적으로 가장 작은 상태 순으로 정렬하고 싶음.
/// AccountId가 맨위에 오도록 하고 싶다.
#[derive(Eq, PartialEq)]
struct OrderedValidatorStake(ValidatorStake);
impl OrderedValidatorStake {
    fn key(&self) -> impl Ord + '_ {
        (self.0.stake(), std::cmp::Reverse(self.0.account_id()))
    }
}
impl PartialOrd for OrderedValidatorStake {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OrderedValidatorStake {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(&other.key())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use near_crypto::{KeyType, PublicKey};
    use near_primitives::epoch_manager::epoch_info::{EpochInfo, EpochInfoV3};
    use near_primitives::epoch_manager::ValidatorSelectionConfig;
    use near_primitives::shard_layout::ShardLayout;
    use near_primitives::types::validator_stake::ValidatorStake;
    use near_primitives::version::PROTOCOL_VERSION;
    use num_rational::Ratio;

    #[test]
    fn test_validator_assignment_all_block_producers() {
        // A simple sanity test. Given fewer proposals than the number of seats,
        // none of which has too little stake, they all get assigned as block and
        // chunk producers.
        let epoch_config = create_epoch_config(2, 100, 0, Default::default());
        let prev_epoch_height = 7;
        let prev_epoch_info = create_prev_epoch_info(prev_epoch_height, &["test1", "test2"], &[]);
        let proposals = create_proposals(&[("test1", 1000), ("test2", 2000), ("test3", 300)]);
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            proposals.clone(),
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        // increment height
        assert_eq!(epoch_info.epoch_height(), prev_epoch_height + 1);

        // assign block producers in decreasing order of stake
        let mut sorted_proposals = proposals;
        sorted_proposals.sort_unstable_by(|a, b| b.stake().cmp(&a.stake()));
        assert_eq!(sorted_proposals, epoch_info.validators_iter().collect::<Vec<_>>());

        // All proposals become block producers
        assert_eq!(epoch_info.block_producers_settlement(), &[0, 1, 2]);
        assert_eq!(epoch_info.fishermen_iter().len(), 0);

        // Validators are split between chunks to make roughly equal stakes
        // (in this case shard 0 has 2000, while shard 1 has 1300).
        assert_eq!(epoch_info.chunk_producers_settlement(), &[vec![0], vec![1, 2]]);
    }

    #[test]
    fn test_validator_assignment_with_chunk_only_producers() {
        // A more complex test. Here there are more BP proposals than spots, so some will
        // become chunk-only producers, along side the other chunk-only proposals.
        let num_bp_seats = 10;
        let num_cp_seats = 30;
        let epoch_config = create_epoch_config(
            2,
            num_bp_seats,
            // purposely set the fishermen threshold high so that none become fishermen
            10_000,
            ValidatorSelectionConfig {
                num_chunk_only_producer_seats: num_cp_seats,
                minimum_validators_per_shard: 1,
                minimum_stake_ratio: Ratio::new(160, 1_000_000),
            },
        );
        let prev_epoch_height = 3;
        let test1_stake = 1000;
        let prev_epoch_info = create_prev_epoch_info(
            prev_epoch_height,
            &[
                // test1 is not included in proposals below, and will get kicked out because
                // their stake is too low.
                ("test1", test1_stake, Proposal::BlockProducer),
                // test2 submitted a new proposal, so their stake will come from there, but it
                // too will be kicked out
                ("test2", 1234, Proposal::ChunkOnlyProducer),
            ],
            &[],
        );
        let proposals = create_proposals((2..(2 * num_bp_seats + num_cp_seats)).map(|i| {
            (
                format!("test{}", i),
                2000u128 + (i as u128),
                if i <= num_cp_seats {
                    Proposal::ChunkOnlyProducer
                } else {
                    Proposal::BlockProducer
                },
            )
        }));
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            proposals.clone(),
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        assert_eq!(epoch_info.epoch_height(), prev_epoch_height + 1);

        // the top stakes are the chosen block producers
        let mut sorted_proposals = proposals;
        sorted_proposals.sort_unstable_by(|a, b| b.stake().cmp(&a.stake()));
        assert!(sorted_proposals.iter().take(num_bp_seats as usize).cloned().eq(epoch_info
            .block_producers_settlement()
            .into_iter()
            .map(|id| epoch_info.get_validator(*id))));

        // stakes are evenly distributed between shards
        assert_eq!(
            stake_sum(&epoch_info, epoch_info.chunk_producers_settlement()[0].iter()),
            stake_sum(&epoch_info, epoch_info.chunk_producers_settlement()[1].iter()),
        );

        // The top proposals are all chunk producers
        let mut chosen_chunk_producers: Vec<ValidatorStake> = epoch_info
            .chunk_producers_settlement()
            .into_iter()
            .flatten()
            .map(|id| epoch_info.get_validator(*id))
            .collect();
        chosen_chunk_producers.sort_unstable_by(|a, b| b.stake().cmp(&a.stake()));
        assert!(sorted_proposals
            .into_iter()
            .take((num_bp_seats + num_cp_seats) as usize)
            .eq(chosen_chunk_producers));

        // the old, low-stake proposals were not accepted
        let kickout = epoch_info.validator_kickout();
        assert_eq!(kickout.len(), 2);
        assert_eq!(
            kickout.get("test1").unwrap(),
            &ValidatorKickoutReason::NotEnoughStake { stake: test1_stake, threshold: 2011 },
        );
        assert_eq!(
            kickout.get("test2").unwrap(),
            &ValidatorKickoutReason::NotEnoughStake { stake: 2002, threshold: 2011 },
        );
    }

    #[test]
    fn test_block_producer_sampling() {
        let num_shards = 4;
        let epoch_config = create_epoch_config(
            num_shards,
            2,
            0,
            ValidatorSelectionConfig {
                num_chunk_only_producer_seats: 0,
                minimum_validators_per_shard: 1,
                minimum_stake_ratio: Ratio::new(160, 1_000_000),
            },
        );
        let prev_epoch_height = 7;
        let prev_epoch_info = create_prev_epoch_info(prev_epoch_height, &["test1", "test2"], &[]);
        let proposals = create_proposals(&[("test1", 1000), ("test2", 2000)]);

        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            proposals,
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        // test2 is chosen as the bp 2x more often than test1
        let mut counts: [i32; 2] = [0, 0];
        for h in 0..100_000 {
            let bp = epoch_info.sample_block_producer(h);
            counts[bp as usize] += 1;
        }
        let diff = (2 * counts[1] - counts[0]).abs();
        assert!(diff < 100);
    }

    #[test]
    fn test_chunk_producer_sampling() {
        // When there is 1 CP per shard, they are chosen 100% of the time.
        let num_shards = 4;
        let epoch_config = create_epoch_config(
            num_shards,
            2 * num_shards,
            0,
            ValidatorSelectionConfig {
                num_chunk_only_producer_seats: 0,
                minimum_validators_per_shard: 1,
                minimum_stake_ratio: Ratio::new(160, 1_000_000),
            },
        );
        let prev_epoch_height = 7;
        let prev_epoch_info = create_prev_epoch_info(prev_epoch_height, &["test1", "test2"], &[]);
        let proposals =
            create_proposals(&[("test1", 1000), ("test2", 1000), ("test3", 1000), ("test4", 1000)]);

        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            proposals,
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        for shard_id in 0..num_shards {
            for h in 0..100_000 {
                let cp = epoch_info.sample_chunk_producer(h, shard_id);
                // Don't read too much into this. The reason the ValidatorId always
                // equals the ShardId is because the validators are assigned to shards in order.
                assert_eq!(cp, shard_id)
            }
        }

        // When there are multiple CPs they are chosen in proportion to stake.
        let proposals = create_proposals((1..=num_shards).flat_map(|i| {
            // Each shard gets a pair of validators, one with twice as
            // much stake as the other.
            vec![(format!("test{}", i), 1000), (format!("test{}", 100 * i), 2000)].into_iter()
        }));
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            proposals,
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        for shard_id in 0..num_shards {
            let mut counts: [i32; 2] = [0, 0];
            for h in 0..100_000 {
                let cp = epoch_info.sample_chunk_producer(h, shard_id);
                // if ValidatorId is in the second half then it is the lower
                // stake validator (because they are sorted by decreasing stake).
                let index = if cp >= num_shards { 1 } else { 0 };
                counts[index] += 1;
            }
            let diff = (2 * counts[1] - counts[0]).abs();
            assert!(diff < 500);
        }
    }

    #[test]
    fn test_validator_assignment_ratio_condition() {
        // There are more seats than proposals, however the
        // lower proposals are too small relative to the total
        // (the reason we can't choose them is because the the probability of them actually
        // being selected to make a block would be too low since it is done in
        // proportion to stake).
        let epoch_config = create_epoch_config(
            1,
            100,
            150,
            ValidatorSelectionConfig {
                num_chunk_only_producer_seats: 300,
                minimum_validators_per_shard: 1,
                // for example purposes, we choose a higher ratio than in production
                minimum_stake_ratio: Ratio::new(1, 10),
            },
        );
        let prev_epoch_height = 7;
        // test5 and test6 are going to get kicked out for not enough stake.
        let prev_epoch_info = create_prev_epoch_info(prev_epoch_height, &["test5", "test6"], &[]);
        let proposals = create_proposals(&[
            ("test1", 1000),
            ("test2", 1000),
            ("test3", 1000), // the total up to this point is 3000
            ("test4", 200),  // 200 is < 1/10 of 3000, so not validator, but can be fisherman
            ("test5", 100),  // 100 is even too small to be a fisherman, cannot get any role
            ("test6", 50),
        ]);
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            proposals,
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        // stake below validator threshold, but above fishermen threshold become fishermen
        let fishermen: Vec<_> = epoch_info.fishermen_iter().map(|v| v.take_account_id()).collect();
        assert_eq!(fishermen, vec!["test4".parse().unwrap()]);

        // too low stakes are kicked out
        let kickout = epoch_info.validator_kickout();
        assert_eq!(kickout.len(), 2);
        #[cfg(feature = "protocol_feature_fix_staking_threshold")]
        let expected_threshold = 334;
        #[cfg(not(feature = "protocol_feature_fix_staking_threshold"))]
        let expected_threshold = 300;
        assert_eq!(
            kickout.get("test5").unwrap(),
            &ValidatorKickoutReason::NotEnoughStake { stake: 100, threshold: expected_threshold },
        );
        assert_eq!(
            kickout.get("test6").unwrap(),
            &ValidatorKickoutReason::NotEnoughStake { stake: 50, threshold: expected_threshold },
        );

        let bp_threshold = epoch_info.seat_price();
        let num_validators = epoch_info.validators_iter().len();
        let proposals = create_proposals(&[
            ("test1", 1000),
            ("test2", 1000),
            ("test3", 1000), // the total up to this point is 3000
            ("test4", 200),  // 200 is < 1/10 of 3000, so not validator, but can be fisherman
            ("test5", 100),  // 100 is even too small to be a fisherman, cannot get any role
            ("test6", 50),
            ("test7", bp_threshold),
        ]);
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &epoch_info,
            proposals,
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();
        #[cfg(feature = "protocol_feature_fix_staking_threshold")]
        assert_eq!(num_validators + 1, epoch_info.validators_iter().len());

        let proposals = create_proposals(&[
            ("test1", 1000),
            ("test2", 1000),
            ("test3", 1000), // the total up to this point is 3000
            ("test4", 200),  // 200 is < 1/10 of 3000, so not validator, but can be fisherman
            ("test5", 100),  // 100 is even too small to be a fisherman, cannot get any role
            ("test6", 50),
            ("test7", bp_threshold - 1),
        ]);
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &epoch_info,
            proposals,
            Default::default(),
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();
        assert_eq!(num_validators, epoch_info.validators_iter().len());
    }

    #[test]
    fn test_validator_assignment_with_kickout() {
        // kicked out validators are not selected
        let epoch_config = create_epoch_config(1, 100, 0, Default::default());
        let prev_epoch_height = 7;
        let prev_epoch_info = create_prev_epoch_info(
            prev_epoch_height,
            &[("test1", 10_000), ("test2", 2000), ("test3", 3000)],
            &[],
        );
        let mut kick_out = HashMap::new();
        // test1 is kicked out
        kick_out.insert("test1".parse().unwrap(), ValidatorKickoutReason::Unstaked);
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            Default::default(),
            kick_out,
            Default::default(),
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        // test1 is not selected
        assert_eq!(epoch_info.get_validator_id(&"test1".parse().unwrap()), None);
    }

    #[test]
    fn test_validator_assignment_with_rewards() {
        // validator balances are updated based on their rewards
        let validators = [("test1", 3000), ("test2", 2000), ("test3", 1000)];
        let rewards: [u128; 3] = [7, 8, 9];
        let epoch_config = create_epoch_config(1, 100, 0, Default::default());
        let prev_epoch_height = 7;
        let prev_epoch_info = create_prev_epoch_info(prev_epoch_height, &validators, &[]);
        let rewards_map = validators
            .iter()
            .zip(rewards.iter())
            .map(|((name, _), reward)| (name.parse().unwrap(), *reward))
            .collect();
        let epoch_info = proposals_to_epoch_info(
            &epoch_config,
            [0; 32],
            &prev_epoch_info,
            Default::default(),
            Default::default(),
            rewards_map,
            0,
            PROTOCOL_VERSION,
            PROTOCOL_VERSION,
        )
        .unwrap();

        for (v, ((_, stake), reward)) in
            epoch_info.validators_iter().zip(validators.iter().zip(rewards.iter()))
        {
            assert_eq!(v.stake(), stake + reward);
        }
    }

    /// stake 합계?
    fn stake_sum<'a, I: IntoIterator<Item = &'a u64>>(
        epoch_info: &EpochInfo,
        validator_ids: I,
    ) -> u128 {
        validator_ids.into_iter().map(|id| epoch_info.get_validator(*id).stake()).sum()
    }

    /// Create EpochConfig, only filling in the fields important for validator selection.
    fn create_epoch_config(
        num_shards: u64,
        num_block_producer_seats: u64,
        fishermen_threshold: Balance,
        validator_selection_config: ValidatorSelectionConfig,
    ) -> EpochConfig {
        EpochConfig {
            epoch_length: 10,
            num_block_producer_seats,
            num_block_producer_seats_per_shard: vec![num_block_producer_seats; num_shards as usize],
            avg_hidden_validator_seats_per_shard: vec![0; num_shards as usize],
            block_producer_kickout_threshold: 0,
            chunk_producer_kickout_threshold: 0,
            validator_max_kickout_stake_perc: 100,
            online_min_threshold: 0.into(),
            online_max_threshold: 0.into(),
            fishermen_threshold,
            minimum_stake_divisor: 0,
            protocol_upgrade_stake_threshold: 0.into(),
            shard_layout: ShardLayout::v0(num_shards, 0),
            validator_selection_config,
        }
    }

    fn create_prev_epoch_info<T: IntoValidatorStake + Copy>(
        epoch_height: u64,
        prev_validators: &[T],
        prev_fishermen: &[T],
    ) -> EpochInfo {
        let mut result: EpochInfoV3 = Default::default();

        result.epoch_height = epoch_height;
        result.validators = create_proposals(prev_validators);
        result.fishermen = create_proposals(prev_fishermen);

        result.validator_to_index = to_map(&result.validators);
        result.fishermen_to_index = to_map(&result.fishermen);

        EpochInfo::V3(result)
    }

    fn to_map(vs: &[ValidatorStake]) -> HashMap<AccountId, ValidatorId> {
        vs.iter().enumerate().map(|(i, v)| (v.account_id().clone(), i as u64)).collect()
    }

    /// 제안 생성하는 메서드?
    fn create_proposals<I, T>(ps: I) -> Vec<ValidatorStake>
    where
        T: IntoValidatorStake,
        I: IntoIterator<Item = T>,
    {
        ps.into_iter().map(IntoValidatorStake::into_validator_stake).collect()
    }

    #[derive(Debug, PartialEq, Eq, Copy, Clone)]
    enum Proposal {
        BlockProducer,
        ChunkOnlyProducer,
    }

    trait IntoValidatorStake {
        fn into_validator_stake(self) -> ValidatorStake;
    }

    impl IntoValidatorStake for &str {
        fn into_validator_stake(self) -> ValidatorStake {
            ValidatorStake::new(self.parse().unwrap(), PublicKey::empty(KeyType::ED25519), 100)
        }
    }

    impl IntoValidatorStake for (&str, Balance) {
        fn into_validator_stake(self) -> ValidatorStake {
            ValidatorStake::new(self.0.parse().unwrap(), PublicKey::empty(KeyType::ED25519), self.1)
        }
    }

    impl IntoValidatorStake for (String, Balance) {
        fn into_validator_stake(self) -> ValidatorStake {
            ValidatorStake::new(self.0.parse().unwrap(), PublicKey::empty(KeyType::ED25519), self.1)
        }
    }

    impl IntoValidatorStake for (&str, Balance, Proposal) {
        fn into_validator_stake(self) -> ValidatorStake {
            ValidatorStake::new(self.0.parse().unwrap(), PublicKey::empty(KeyType::ED25519), self.1)
        }
    }

    impl IntoValidatorStake for (String, Balance, Proposal) {
        fn into_validator_stake(self) -> ValidatorStake {
            ValidatorStake::new(self.0.parse().unwrap(), PublicKey::empty(KeyType::ED25519), self.1)
        }
    }

    impl<T: IntoValidatorStake + Copy> IntoValidatorStake for &T {
        fn into_validator_stake(self) -> ValidatorStake {
            (*self).into_validator_stake()
        }
    }
}
