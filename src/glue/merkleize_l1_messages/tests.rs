use super::input::MESSAGE_SERIALIZATION_BYTES as LEAF_LENGTH;
use super::merkleize::{is_power_of_n, merkleize_l1_messages_inner};
use super::tree_hasher::*;
use super::*;
use crate::circuit_structures::byte::Byte;
use crate::circuit_structures::traits::CircuitArithmeticRoundFunction;
use crate::franklin_crypto::bellman::bn256::{Bn256, Fr};
use crate::franklin_crypto::bellman::plonk::better_better_cs::cs::ConstraintSystem;
use crate::franklin_crypto::bellman::{Engine, PrimeField};
use crate::franklin_crypto::bellman::{Field, SynthesisError};
use crate::franklin_crypto::plonk::circuit::allocated_num::Num;
use crate::franklin_crypto::plonk::circuit::bigint::fe_to_biguint;
use crate::franklin_crypto::plonk::circuit::boolean::Boolean;
use crate::franklin_crypto::plonk::circuit::hashes_with_tables::keccak::gadgets::Keccak256Gadget;
use crate::franklin_crypto::plonk::circuit::hashes_with_tables::sha256::gadgets::Sha256Gadget;
use crate::franklin_crypto::plonk::circuit::tables::inscribe_default_range_table_for_bit_width_over_first_three_columns;
use crate::glue::traits::CircuitFixedLengthEncodable;
use crate::scheduler::queues::*;
use crate::testing::{create_test_artifacts, deterministic_rng};
use crate::utils::log2_floor;
use crate::vm::optimizer::sponge_set::SpongeOptimizer;
use crate::vm::primitives::small_uints::*;
use rand::Rng;
use sha2::{Digest, Sha256};
use std::convert::TryInto;

pub trait TreeHasher {
    fn hash(input: &[u8]) -> [u8; 32];
    fn node_hash<const ARITY: usize>(nodes: &[[u8; 32]; ARITY]) -> [u8; 32] {
        let mut concatenated = vec![];
        for node in nodes {
            concatenated.extend_from_slice(node);
        }
        Self::hash(&concatenated)
    }
}

#[derive(Clone, Debug)]
pub struct KeccakTreeHasher;

impl TreeHasher for KeccakTreeHasher {
    fn hash(input: &[u8]) -> [u8; 32] {
        let mut state = Keccak::new_keccak256();
        state.update(input);
        let mut output = [0; 32];
        state.finalize(&mut output);

        output
    }
}

pub struct Sha256TreeHasher;

impl TreeHasher for Sha256TreeHasher {
    fn hash(input: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&input);
        hasher.finalize().into()
    }
}

pub fn compute_merkle_root_from_leafs_generic<
    E: Engine,
    H: TreeHasher,
    const N: usize,
    const ARITY: usize,
>(
    leafs: &[[u8; N]],
) -> [u8; 32] {
    let num_leafs = leafs.len();
    assert!(
        is_power_of_n(num_leafs, ARITY),
        "number of leafs is not power of {}",
        ARITY
    );

    let depth = if ARITY == 2 {
        log2_floor(num_leafs) as usize
    } else if ARITY == 4 {
        (log2_floor(num_leafs) / 2) as usize
    } else {
        unimplemented!("only 4ary or 2ary are allowed")
    };

    let mut all_layers = vec![];
    let mut node_hashes = vec![];
    for leaf in leafs.iter() {
        let node_hash = H::hash(&leaf[..]);
        node_hashes.push(node_hash);
    }
    all_layers.push(node_hashes);
    for _ in 0..depth {
        let previous_node_hashes = all_layers.last().unwrap();
        assert!(previous_node_hashes.len() > 1);
        let mut layer = vec![];
        for chunk in previous_node_hashes.chunks(ARITY) {
            let nodes: [[u8; 32]; ARITY] = chunk.try_into().unwrap();
            let hash = H::node_hash(&nodes);
            layer.push(hash);
        }
        drop(previous_node_hashes);
        all_layers.push(layer);
    }

    let root = all_layers.last().unwrap()[0];

    root
}

fn init_tree_hashers<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
) -> Result<(CircuitKeccakTreeHasher<E>, CircuitSha256TreeHasher<E>), SynthesisError> {
    Ok((
        CircuitKeccakTreeHasher::new(cs)?,
        CircuitSha256TreeHasher::new(cs)?,
    ))
}

fn pad_bytes(bytes: &mut Vec<u8>, size: usize) {
    assert!(bytes.len() <= size);
    bytes.reverse();
    bytes.resize(size, 0);
    bytes.reverse();
}

fn init_rand_array<R: Rng, const N: usize, const ARITY: usize>(
    rng: &mut R,
    num_items: usize,
) -> Vec<[[u8; N]; ARITY]> {
    let mut outputs = vec![];
    for _ in 0..num_items {
        let mut output = [[0u8; N]; ARITY];
        for out in output.iter_mut() {
            for o in out.iter_mut() {
                *o = rng.gen()
            }
        }

        outputs.push(output);
    }

    outputs
}

// #[test]
// fn test_merkelize() -> Result<(), SynthesisError> {
//     let rng = &mut deterministic_rng();
//     let (mut cs, round_function, _) = create_test_artifacts();
//     let cs = &mut cs;
//     inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

//     let (keccak_tree_hasher, sha256_tree_hasher) = init_tree_hashers(cs)?;
//     {
//         println!("Testing keccak256 arity = 2");
//         // keccak 2ary
//         const LIMIT: usize = 8;
//         const ARITY: usize = 2;
//         let start = cs.n();
//         merklize::<_, _,  KeccakTreeHasher, _, _, _, ARITY>(
//             cs,
//             &keccak_tree_hasher,
//             rng,
//             &round_function,
//             LIMIT
//         )?;

//         println!("keccak with 2-arity takes {} gates", cs.n() - start);

//         assert!(cs.is_satisfied());
//     }
//     {
//         println!("Testing keccak256 arity = 4");
//         // keccak 4ary
//         const LIMIT: usize = 16;
//         const ARITY: usize = 4;
//         let start = cs.n();
//         merklize::<_, _, KeccakTreeHasher, _, _, _, ARITY>(
//             cs,
//             &keccak_tree_hasher,
//             rng,
//             &round_function,
//             LIMIT
//         )?;

//         println!("keccak with 4-arity takes {} gates", cs.n() - start);

//         assert!(cs.is_satisfied());
//     }
//     {
//         println!("Testing sha256 arity = 2");
//         // sha256 2ary
//         const LIMIT: usize = 8;
//         const ARITY: usize = 2;
//         let start = cs.n();
//         merklize::<_, _, Sha256TreeHasher, _, _, _, ARITY>(
//             cs,
//             &sha256_tree_hasher,
//             rng,
//             &round_function,
//             LIMIT
//         )?;

//         println!("sha256 with 2-arity takes {} gates", cs.n() - start);

//         assert!(cs.is_satisfied());
//     }
//     {
//         println!("Testing sha256 arity = 4");
//         // sha256 4ary
//         const LIMIT: usize = 16;
//         const ARITY: usize = 4;
//         let start = cs.n();
//         merklize::<_, _, Sha256TreeHasher, _, _, _, ARITY>(
//             cs,
//             &sha256_tree_hasher,
//             rng,
//             &round_function,
//             LIMIT
//         )?;

//         println!("sha256 with 4-arity takes {} gates", cs.n() - start);

//         assert!(cs.is_satisfied());
//     }

//     Ok(())
// }

// fn merklize<
//     E: Engine,
//     CS: ConstraintSystem<E>,
//     H: TreeHasher,
//     CH: CircuitTreeHasher<E>,
//     RNG: Rng,
//     R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
//     const ARITY: usize,
// >(
//     cs: &mut CS,
//     circuit_tree_hasher: &CH,
//     rng: &mut RNG,
//     round_function: &R,
//     limit: usize,
// ) -> Result<(), SynthesisError> {
//     let mut queue = SortedStorageItemsQueue::empty();
//     let mut linear_concatenation_bytes = vec![];
//     let mut all_leafs = vec![];
//     for idx in 0..limit {
//         // witnesses
//         let actor = u160::from_u64(rng.gen());
//         let target = u160::from_u64(rng.gen());
//         let actor_as_biguint = <u160 as Into<BigUint>>::into(actor);
//         let key = fe_to_biguint::<E::Fr>(&rng.gen());
//         let value = fe_to_biguint::<E::Fr>(&rng.gen());
//         let r_w_flag = rng.gen();
//         let target_is_zkporter = rng.gen();

//         let mut actor_bytes = actor_as_biguint.to_bytes_be();
//         pad_bytes(&mut actor_bytes, 20);
//         let mut key_bytes = key.to_bytes_be();
//         pad_bytes(&mut key_bytes, 32);
//         let mut value_bytes = value.to_bytes_be();
//         pad_bytes(&mut value_bytes, 32);

//         linear_concatenation_bytes.extend_from_slice(&actor_bytes);
//         linear_concatenation_bytes.extend_from_slice(&key_bytes);
//         linear_concatenation_bytes.extend_from_slice(&value_bytes);

//         let wit = SortedStorageLogItemWitness {
//             actor,
//             target,
//             key,
//             value,
//             r_w_flag,
//             target_is_zkporter,
//             _marker: std::marker::PhantomData,
//         };

//         let mut leaf = [0u8; LEAF_LENGTH];
//         leaf[0..20].copy_from_slice(&actor_bytes);
//         leaf[20..(20+32)].copy_from_slice(&key_bytes);
//         leaf[(20+32)..].copy_from_slice(&value_bytes);

//         all_leafs.push(leaf);

//         let allocated_item = SortedStorageLogItem::alloc_from_witness(cs, Some(wit))?;
//         queue.push(
//             cs,
//             &allocated_item,
//             &Boolean::Constant(true),
//             round_function,
//         )?;
//     }

//     let expected_merkle_root_bytes =
//         compute_merkle_root_from_leafs_generic::<E, H, LEAF_LENGTH, ARITY>(&all_leafs);

//     let expected_linear_hash_bytes = H::hash(&linear_concatenation_bytes);

//     let (claimed_merkle_root, hash_of_all_leafs) = merkleize_l1_messages_inner::<_, _, _, _, 2, 3, ARITY>(
//         cs,
//         queue,
//         round_function,
//         circuit_tree_hasher,
//         limit,
//     )?;

//     for (e, c) in expected_merkle_root_bytes.iter().zip(claimed_merkle_root){
//         assert_eq!(*e, c.get_byte_value().unwrap())
//     }

//     for (e, c) in expected_linear_hash_bytes.iter().zip(hash_of_all_leafs){
//         assert_eq!(*e, c.get_byte_value().unwrap())
//     }

//     Ok(())
// }
