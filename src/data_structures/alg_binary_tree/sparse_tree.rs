use super::*;
use crate::bellman::worker::Worker;
use crate::derivative::*;
use crate::pairing::*;
use crate::utils::log2_floor;
use std::collections::HashMap;
use std::fmt;

#[derive(Derivative)]
#[derivative(Clone)]
pub(crate) struct TreeLevel<T: Copy + Clone> {
    default_hash: T,
    custom_hashes: HashMap<usize, T>,
}

// This binary tree owns leaf hashes, but does not own values
#[derive(Derivative)]
#[derivative(Clone)]
pub struct BinaryTree<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> {
    depth: usize,
    nodes: Vec<TreeLevel<H::InOut>>,
    tree_hasher: H,
    _marker: std::marker::PhantomData<E>,
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> BinaryTree<E, H> {
    /// Creates new tree where all leaf hashes are same
    pub fn new(depth: usize, default_leaf_hash: H::InOut, tree_hasher: H) -> Self {
        let mut nodes = vec![TreeLevel {
            default_hash: default_leaf_hash,
            custom_hashes: HashMap::new(),
        }];

        let mut current_hash = default_leaf_hash;
        for level in (0..depth).rev() {
            current_hash = tree_hasher.node_hash(&[current_hash, current_hash], level);
            nodes.push(TreeLevel {
                default_hash: current_hash,
                custom_hashes: HashMap::new(),
            });
        }
        nodes.reverse();

        Self {
            depth,
            nodes,
            tree_hasher,
            _marker: Default::default(),
        }
    }

    /// Gets node from the tree, `index` is level-specific index of the node.
    pub fn get_node(&self, level: usize, index: usize) -> H::InOut {
        let level = &self.nodes[level];
        match level.custom_hashes.get(&index) {
            None => level.default_hash,
            Some(hash) => *hash,
        }
    }

    pub fn get_leaf(&self, index: usize) -> H::InOut {
        self.get_node(self.depth, index)
    }

    fn make_full_path(&self, leaf_index: usize) -> Vec<H::InOut> {
        let mut path = vec![];

        let mut current_idx = leaf_index;
        for level in (1..self.depth + 1).rev() {
            let sibling_idx = current_idx ^ 1;
            path.push(self.get_node(level, sibling_idx));
            current_idx /= 2;
        }

        path
    }

    pub fn size(&self) -> usize {
        self.depth
    }

    pub fn create_from_leaf_hashes(leaf_hashes: &[H::InOut], tree_hasher: H) -> Self {
        let num_leafs = leaf_hashes.len();
        assert!(num_leafs.is_power_of_two(), "tree must be binary");
        let depth = log2_floor(num_leafs) as usize;

        let leaf_level = {
            let mut leaf_hashes_map = HashMap::new();
            for (index, hash) in leaf_hashes.iter().enumerate() {
                leaf_hashes_map.insert(index, *hash);
            }

            TreeLevel {
                default_hash: H::placeholder_output(), // doesn't matter since all hashes are manually set
                custom_hashes: leaf_hashes_map,
            }
        };
        let mut nodes = vec![leaf_level];

        for level in (0..depth).rev() {
            let mut custom_hashes = HashMap::new();
            let child_hashes = &nodes.last().unwrap().custom_hashes;
            for i in 0..1 << level {
                let left = child_hashes.get(&(i * 2)).unwrap();
                let right = child_hashes.get(&(i * 2 + 1)).unwrap();

                let hash = tree_hasher.node_hash(&[*left, *right], level);
                custom_hashes.insert(i, hash);
            }
            nodes.push(TreeLevel {
                default_hash: H::placeholder_output(),
                custom_hashes,
            })
        }
        nodes.reverse();

        Self {
            depth,
            nodes,
            tree_hasher,
            _marker: Default::default(),
        }
    }

    pub fn get_commitment(&self) -> H::InOut {
        self.get_node(0, 0)
    }

    pub fn produce_query(&self, leaf_index: usize) -> QueryPath<E, H> {
        QueryPath::<E, H> {
            index: leaf_index,
            leaf_hash: self.get_leaf(leaf_index),
            path: self.make_full_path(leaf_index),
        }
    }

    pub fn verify_path(commitment: &H::InOut, query: &QueryPath<E, H>, tree_hasher: &H) -> bool {
        let mut hash = query.leaf_hash();
        let mut idx = query.index();
        let mut hash_input = [H::placeholder_output(); 2];

        dbg!(&query);

        for el in query.path.iter() {
            {
                if idx & 1 == 0 {
                    hash_input[0] = hash;
                    hash_input[1] = *el;
                } else {
                    hash_input[0] = *el;
                    hash_input[1] = hash;
                }
            }
            hash = tree_hasher.node_hash(&hash_input, 0);
            idx >>= 1;

            dbg!(&hash_input, &hash);
        }

        &hash == commitment
    }

    pub fn update_leaf(&mut self, leaf_index: usize, leaf_hash: H::InOut) {
        self.nodes[self.depth]
            .custom_hashes
            .insert(leaf_index, leaf_hash);

        let mut current_idx = leaf_index / 2;
        for level in (0..self.depth).rev() {
            let left_idx = current_idx * 2;
            let right_idx = current_idx * 2 + 1;

            let left_hash = self.get_node(level + 1, left_idx);
            let right_hash = self.get_node(level + 1, right_idx);

            let current_hash = self.tree_hasher.node_hash(&[left_hash, right_hash], level);

            self.nodes[level]
                .custom_hashes
                .insert(current_idx, current_hash);

            current_idx /= 2;
        }
    }
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> PartialEq for BinaryTree<E, H> {
    fn eq(&self, other: &Self) -> bool {
        self.get_commitment() == other.get_commitment()
    }
}

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> Eq for BinaryTree<E, H> {}

#[derive(Clone, PartialEq, Eq)]
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

impl<E: Engine, H: AlgebraicBinaryTreeInnerHasher<E::Fr>> fmt::Debug for QueryPath<E, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("QueryPath")
            .field("index", &self.index)
            .field("path", &self.path)
            .field("leaf_hash", &self.leaf_hash)
            .finish()
    }
}
