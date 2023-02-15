use super::*;
use crate::bellman::worker::Worker;
use crate::derivative::*;
use crate::pairing::*;
use crate::utils::log2_floor;

// This binary tree owns leaf hashes, but does not own
#[derive(Derivative)]
#[derivative(Clone)]
pub struct BinaryTree<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> {
    pub(crate) size: usize,
    pub(crate) num_leafs: usize,
    pub(crate) nodes: Vec<H::InOut>,
    pub(crate) tree_hasher: H,
    _marker: std::marker::PhantomData<E>,
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> BinaryTree<E, H> {
    fn make_full_path(&self, leaf_index: usize, leaf_pair_hash: H::InOut) -> Vec<H::InOut> {
        // we already have a pair hash for this leaf, so we only proceed to next levels
        let half_len = self.nodes.len() / 2;
        let mut nodes = &self.nodes[..half_len];

        let mut path = vec![];
        path.push(leaf_pair_hash);

        let mut idx = leaf_index;
        idx >>= 1;

        for _ in 0..log2_floor(nodes.len() / 2) {
            let half_len = nodes.len() / 2;
            let (next_level, this_level) = nodes.split_at(half_len);
            let pair_idx = idx ^ 1usize;
            let value = this_level[pair_idx];
            path.push(value);
            idx >>= 1;
            nodes = next_level;
        }

        path
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn num_leafs(&self) -> usize {
        self.num_leafs
    }

    pub fn create_from_leaf_hashes(leaf_hashes: &[H::InOut], tree_hasher: H) -> Self {
        let num_leafs = leaf_hashes.len();
        assert!(num_leafs.is_power_of_two(), "tree must be binary");

        // we keep leaf hashes and all next sequences of nodes
        let num_nodes = num_leafs * 2;

        let mut nodes = vec![H::placeholder_output(); num_nodes];
        (&mut nodes[num_leafs..]).copy_from_slice(leaf_hashes);

        let worker = Worker::new();

        let hasher_ref = &tree_hasher;

        let num_levels = log2_floor(num_leafs) as usize;

        let mut nodes_for_hashing = &mut nodes[..];

        for _level in (0..num_levels).rev() {
            // do the trick - split
            let (next_levels, inputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len() / 2);
            let (_, outputs) = next_levels.split_at_mut(next_levels.len() / 2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk).zip(inputs.chunks(chunk * 2)) {
                    scope.spawn(move |_| {
                        let mut hash_input = [H::placeholder_output(); 2];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0] = i[0];
                            hash_input[1] = i[1];
                            *o = hasher_ref.node_hash(&hash_input, _level);
                        }
                    });
                }
            });

            nodes_for_hashing = next_levels;
        }

        Self {
            size: num_leafs,
            num_leafs: num_leafs,
            nodes: nodes,
            tree_hasher: tree_hasher,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn get_commitment(&self) -> H::InOut {
        self.nodes[1].clone()
    }

    pub fn produce_query(&self, leaf_index: usize) -> QueryPath<E, H> {
        let offset = self.nodes.len() / 2;

        let index = leaf_index + offset;
        let pair_index = (leaf_index ^ 1) + offset;

        let leaf_hash = self.nodes[index];
        let leaf_pair_hash = self.nodes[pair_index];

        let path = self.make_full_path(leaf_index, leaf_pair_hash);

        QueryPath::<E, H> {
            index: index,
            leaf_hash: leaf_hash,
            path: path,
        }
    }

    pub fn verify_path(commitment: &H::InOut, query: &QueryPath<E, H>, tree_hasher: &H) -> bool {
        let mut hash = query.leaf_hash();
        let mut idx = query.index();
        let mut hash_input = [H::placeholder_output(); 2];

        for el in query.path.iter() {
            {
                if idx & 1usize == 0 {
                    hash_input[0] = hash;
                    hash_input[1] = *el;
                } else {
                    hash_input[0] = *el;
                    hash_input[1] = hash;
                }
            }
            hash = tree_hasher.node_hash(&hash_input, 0);
            idx >>= 1;
        }

        &hash == commitment
    }
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> PartialEq for BinaryTree<E, H> {
    fn eq(&self, other: &Self) -> bool {
        self.get_commitment() == other.get_commitment()
    }
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> Eq for BinaryTree<E, H> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryPath<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> {
    index: usize,
    path: Vec<H::InOut>,
    leaf_hash: H::InOut,
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> QueryPath<E, H> {
    pub fn index(&self) -> usize {
        self.index
    }

    pub fn path(&self) -> &[H::InOut] {
        &self.path
    }

    pub fn leaf_hash(&self) -> H::InOut {
        self.leaf_hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data_structures::alg_binary_tree::rescue_impl::StaticGenericBinaryTreeHasher;
    use crate::utils::bn254_rescue_params;
    use crate::utils::{AWIDTH_VALUE, SWIDTH_VALUE};
    use franklin_crypto::bellman::pairing::bn256::{Bn256, Fr};
    use rescue_poseidon::RescueParams;

    #[test]
    fn test_create_from_leaves() {
        let params = bn254_rescue_params();
        let hasher = StaticGenericBinaryTreeHasher::<
            Bn256,
            RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
            AWIDTH_VALUE,
            SWIDTH_VALUE,
        >::new(&params);

        let mut leaf_hashes = vec![Fr::zero(); 8];
        let one = Fr::from_str("1").unwrap();
        leaf_hashes[0] = one;
        let new_tree = BinaryTree::<Bn256, _>::create_from_leaf_hashes(&leaf_hashes, hasher);

        assert_eq!(
            new_tree.get_commitment().to_string().as_str(),
            "Fr(0x2a30c843f2912ccc50f7b5baab078e548dd5df3fdb07199d1413c437b0997dee)"
        );
    }

    #[test]
    fn test_query_path() {
        let leaf_hashes = (0..8)
            .map(|leaf| Fr::from_str(0.to_string().as_str()).unwrap())
            .collect::<Vec<_>>();

        let params = bn254_rescue_params();
        let hasher = StaticGenericBinaryTreeHasher::<
            Bn256,
            RescueParams<Bn256, AWIDTH_VALUE, SWIDTH_VALUE>,
            AWIDTH_VALUE,
            SWIDTH_VALUE,
        >::new(&params);

        let tree = BinaryTree::<Bn256, _>::create_from_leaf_hashes(&leaf_hashes, hasher.clone());

        let q = tree.produce_query(0);

        assert!(BinaryTree::verify_path(&tree.get_commitment(), &q, &hasher))
    }
}
