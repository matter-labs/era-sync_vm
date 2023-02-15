use super::*;

// we will have quite a few cases when we would need to select elements
// from some quite shallow trees in recursion, so we can make a structure
// that will hold all the witness for convenience
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ShallowTree<
    E: Engine,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const DEPTH: usize,
> {
    pub leaf_hashes: Option<Vec<E::Fr>>,
    pub node_hashes: Option<Vec<Vec<E::Fr>>>, // for cognitive complexity
    pub max_non_trivial_index: Byte<E>,
    pub round_function: R,
}

impl<
        E: Engine,
        R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
        const DEPTH: usize,
    > ShallowTree<E, R, DEPTH>
{
    pub fn create(
        leaf_hashes: Option<Vec<E::Fr>>,
        round_function: R,
        max_non_trivial_index: Byte<E>,
    ) -> Self {
        assert!(DEPTH <= 8);

        let num_node_layers = DEPTH - 1;
        let node_layers = if let Some(leaf_hashes) = leaf_hashes.as_ref() {
            assert_eq!(leaf_hashes.len(), 1 << DEPTH);
            let mut node_layers: Vec<Vec<_>> = vec![];
            for i in 0..num_node_layers {
                // make borrow checker happy
                let src = if i == 0 {
                    &leaf_hashes
                } else {
                    &node_layers[node_layers.len() - 1]
                };
                let mut layer_elements: Vec<_> = vec![];
                for pair in src.chunks(2) {
                    let node_hash = simulate_variable_length_hash(pair, &round_function);
                    layer_elements.push(node_hash);
                }
                assert!(layer_elements.len().is_power_of_two());
                drop(src);
                node_layers.push(layer_elements);
            }
            assert_eq!(node_layers.last().unwrap().len(), 1);

            Some(node_layers)
        } else {
            None
        };

        Self {
            leaf_hashes,
            node_hashes: node_layers,
            max_non_trivial_index,
            round_function,
        }
    }

    fn path_witness_for_index(&self, index: Option<u8>) -> Option<(E::Fr, [E::Fr; DEPTH])> {
        let index = index?;
        if let Some(max) = self.max_non_trivial_index.get_byte_value() {
            assert!(index <= max);
        }
        let leaf_hashes = self.leaf_hashes.as_ref()?;
        let leaf_value = leaf_hashes[index as usize];

        let mut path_witness = [E::Fr::zero(); DEPTH];
        let pair_value = leaf_hashes[(index ^ 1u8) as usize];
        path_witness[0] = pair_value;
        let node_hashes = self.node_hashes.as_ref()?;
        let mut index = index as usize;
        for (idx, layer) in node_hashes.iter().enumerate() {
            index >>= 1;
            let value = layer[index];
            path_witness[idx + 1] = value;
        }

        Some((leaf_value, path_witness))
    }

    pub fn open_at_index_to_leaf_hash_assuming_root<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        tree_root: Num<E>,
        index: Byte<E>,
        execute: Boolean,
    ) -> Result<Num<E>, SynthesisError> {
        assert!(DEPTH <= 8);
        // check that index is <= max non-trivial
        let max = UInt16::from_num_unchecked(self.max_non_trivial_index.inner);
        let requested_index = UInt16::from_num_unchecked(index.inner);
        let (_, borrow) = max.sub(cs, &requested_index)?;
        can_not_be_false_if_flagged(cs, &borrow.not(), &execute)?;
        // get witness
        let wit = self.path_witness_for_index(index.get_byte_value());
        let (leaf_hash, path_witness) = match wit {
            Some((leaf_hash, path_witness)) => (Some(leaf_hash), Some(path_witness)),
            _ => (None, None),
        };

        let leaf_hash = Num::alloc(cs, leaf_hash)?;
        let path_witness = Num::alloc_multiple(cs, path_witness)?;
        let path = index.inner.into_bits_le(cs, Some(DEPTH))?;
        use std::convert::TryInto;
        let path: [Boolean; DEPTH] = path.try_into().expect("length must match");

        let calculated_root = calculate_to_root_fixed_with_round_function(
            cs,
            &leaf_hash,
            &path_witness,
            &path,
            &self.round_function,
        )?;

        let root_is_equal = Num::equals(cs, &tree_root, &calculated_root)?;
        can_not_be_false_if_flagged(cs, &root_is_equal, &execute)?;

        Ok(leaf_hash)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ShallowItemTree<
    E: Engine,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
    const DEPTH: usize,
> {
    pub leaf_values: Option<Vec<I::Witness>>,
    pub inner: ShallowTree<E, R, DEPTH>,
}

impl<
        E: Engine,
        R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
        const DEPTH: usize,
    > ShallowItemTree<E, R, I, N, DEPTH>
{
    pub fn create<F: Fn(&I::Witness) -> [E::Fr; N]>(
        leaf_values: Option<Vec<I::Witness>>,
        round_function: R,
        max_non_trivial_index: Byte<E>,
        witness_packing_function: F,
    ) -> Self {
        let leaf_hashes = if let Some(leaf_values) = leaf_values.as_ref() {
            let mut leaf_hashes = vec![];
            for v in leaf_values.iter() {
                let encoding = witness_packing_function(v);
                let leaf_hash = simulate_variable_length_hash(&encoding, &round_function);
                leaf_hashes.push(leaf_hash);
            }

            Some(leaf_hashes)
        } else {
            None
        };

        let inner = ShallowTree::create(leaf_hashes, round_function, max_non_trivial_index);

        Self { leaf_values, inner }
    }

    fn item_witness_for_index(&self, index: Option<u8>) -> Option<I::Witness> {
        let index = index?;
        let leaf_values = self.leaf_values.as_ref()?;
        let leaf_value = leaf_values[index as usize].clone();

        Some(leaf_value)
    }

    pub fn open_item_at_index_assuming_root<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        tree_root: Num<E>,
        index: Byte<E>,
        execute: Boolean,
    ) -> Result<I, SynthesisError> {
        let (item, _) =
            self.open_item_and_encoding_at_index_assuming_root(cs, tree_root, index, execute)?;

        Ok(item)
    }

    pub fn open_item_and_encoding_at_index_assuming_root<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        tree_root: Num<E>,
        index: Byte<E>,
        execute: Boolean,
    ) -> Result<(I, [Num<E>; N]), SynthesisError> {
        assert!(DEPTH <= 8);
        // get witness
        let wit = self.item_witness_for_index(index.get_byte_value());
        // allocate
        let item = I::allocate_from_witness(cs, wit)?;
        let encoding = item.encode(cs)?;
        let leaf_hash = variable_length_hash(cs, &encoding, &self.inner.round_function)?;

        let opened_leaf_hash = self
            .inner
            .open_at_index_to_leaf_hash_assuming_root(cs, tree_root, index, execute)?;

        let leaf_hashes_are_equal = Num::equals(cs, &opened_leaf_hash, &leaf_hash)?;
        can_not_be_false_if_flagged(cs, &leaf_hashes_are_equal, &execute)?;

        Ok((item, encoding))
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct RawShallowTree<
    E: Engine,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
    const N: usize,
    const DEPTH: usize,
> {
    pub leaf_values: Option<Vec<[E::Fr; N]>>,
    pub inner: ShallowTree<E, R, DEPTH>,
}

impl<
        E: Engine,
        R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
        const N: usize,
        const DEPTH: usize,
    > RawShallowTree<E, R, N, DEPTH>
{
    pub fn create(
        leaf_values: Option<Vec<[E::Fr; N]>>,
        round_function: R,
        max_non_trivial_index: Byte<E>,
    ) -> Self {
        let leaf_hashes = if let Some(leaf_values) = leaf_values.as_ref() {
            let mut leaf_hashes = vec![];
            for v in leaf_values.iter() {
                let leaf_hash = simulate_variable_length_hash(&v[..], &round_function);
                leaf_hashes.push(leaf_hash);
            }

            Some(leaf_hashes)
        } else {
            None
        };

        let inner = ShallowTree::create(leaf_hashes, round_function, max_non_trivial_index);

        Self { leaf_values, inner }
    }

    fn item_witness_for_index(&self, index: Option<u8>) -> Option<[E::Fr; N]> {
        let index = index?;
        let leaf_values = self.leaf_values.as_ref()?;
        let leaf_value = leaf_values[index as usize].clone();

        Some(leaf_value)
    }

    pub fn open_encoding_at_index_assuming_root<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        tree_root: Num<E>,
        index: Byte<E>,
        execute: Boolean,
    ) -> Result<[Num<E>; N], SynthesisError> {
        assert!(DEPTH <= 8);
        // get witness
        let wit = self.item_witness_for_index(index.get_byte_value());
        // allocate
        let encoding = Num::alloc_multiple(cs, wit)?;
        let leaf_hash = variable_length_hash(cs, &encoding, &self.inner.round_function)?;

        let opened_leaf_hash = self
            .inner
            .open_at_index_to_leaf_hash_assuming_root(cs, tree_root, index, execute)?;

        let leaf_hashes_are_equal = Num::equals(cs, &opened_leaf_hash, &leaf_hash)?;
        can_not_be_false_if_flagged(cs, &leaf_hashes_are_equal, &execute)?;

        Ok(encoding)
    }
}
