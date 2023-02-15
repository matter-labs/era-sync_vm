use crate::bellman::SynthesisError;
use crate::ff::*;
use crate::pairing::*;

use super::*;
use crate::data_structures::alg_binary_tree::dense_tree::*;
use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
use crate::data_structures::alg_binary_tree::*;
use crate::traits::*;
use rescue_poseidon::HashParams;

#[derive(Clone)]
pub struct ToyGenericTree<
    E: Engine,
    T: ArithmeticCommitable<E>,
    P: HashParams<E, AWIDTH, SWIDTH>,
    const AWIDTH: usize,
    const SWIDTH: usize,
> {
    commitment_hasher: GenericHasher<E, P, AWIDTH, SWIDTH>,
    tree_inner_hasher: StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>,

    leafs: Vec<T>,
    tree: BinaryTree<E, StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>>,
}

impl<
        E: Engine,
        T: ArithmeticCommitable<E>,
        P: HashParams<E, AWIDTH, SWIDTH>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    > ToyGenericTree<E, T, P, AWIDTH, SWIDTH>
{
    pub fn new(
        values: Vec<T>,
        leaf_hasher_params: &P,
        node_hasher_params: &P,
    ) -> Result<Self, SynthesisError> {
        let leaf_hasher = GenericHasher::new_from_params(leaf_hasher_params);
        let node_hasher = StaticGenericBinaryTreeHasher::new(node_hasher_params);

        let mut leaf_hashes =
            vec![StaticGenericBinaryTreeHasher::<E, P, AWIDTH, SWIDTH>::placeholder_output()];

        for (idx, el) in values.iter().enumerate() {
            leaf_hashes[idx] = el.commit(&leaf_hasher)?;
        }

        let tree = BinaryTree::create_from_leaf_hashes(&leaf_hashes, node_hasher.clone());

        let new = Self {
            commitment_hasher: leaf_hasher,
            tree_inner_hasher: node_hasher,

            leafs: values,
            tree: tree,
        };

        Ok(new)
    }
}

impl<
        E: Engine,
        T: ArithmeticCommitable<E>,
        P: HashParams<E, AWIDTH, SWIDTH>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    > MerkleTreeBasedStorage<E> for ToyGenericTree<E, T, P, AWIDTH, SWIDTH>
{
    type Value = T;
    type Proof = QueryPath<E, StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>>;

    fn get(&self, index: usize) -> Result<(Self::Value, Self::Proof), SynthesisError> {
        let el = self.leafs[index].clone();

        let proof = self.tree.produce_query(index);

        Ok((el, proof))
    }
    fn set(&mut self, index: usize, new_value: Self::Value) -> Result<(), SynthesisError> {
        self.leafs[index] = new_value;
        let mut leaf_hashes =
            vec![StaticGenericBinaryTreeHasher::<E, P, AWIDTH, SWIDTH>::placeholder_output()];

        for (idx, el) in self.leafs.iter().enumerate() {
            leaf_hashes[idx] = el.commit(&self.commitment_hasher)?;
        }

        let tree = BinaryTree::<E, StaticGenericBinaryTreeHasher<E, P, AWIDTH, SWIDTH>>::create_from_leaf_hashes(
            &leaf_hashes,
            self.tree_inner_hasher.clone()
        );

        self.tree = tree;

        Ok(())
    }
}
