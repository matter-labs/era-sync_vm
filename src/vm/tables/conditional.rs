use super::*;

use num_traits::FromPrimitive;

// first column contain 3-bit encoding of the conditional
// second column contains 3 bit packed encoding of flags in a system
// third column contains 0/1 for conditional flag
#[derive(Clone)]
pub struct ConditionalResolutionTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    name: &'static str,
    table_size: usize,
}

pub const FLAGS_PACKED_ENCODING_BIT_WIDTH: usize = 3;

pub(crate) fn integer_into_flags(encoding: u8) -> (bool, bool, bool) {
    (
        (encoding & 0x1) != 0,
        ((encoding & 0x2) != 0),
        ((encoding & 0x4) != 0),
    )
}

impl<E: Engine> ConditionalResolutionTable<E> {
    pub fn new(name: &'static str) -> Self {
        let num_rows = 8 * 8;
        let mut key_0 = Vec::with_capacity(num_rows);
        let mut key_1 = Vec::with_capacity(num_rows);
        let mut value = Vec::with_capacity(num_rows);
        let mut map = std::collections::HashMap::with_capacity(num_rows);

        let all_conditions = zkevm_opcode_defs::ALL_CONDITIONS;
        use zkevm_opcode_defs::Condition;
        for condition in all_conditions.iter() {
            let x = condition.variant_index(); // integer encoding
            for i in 0..(1 << FLAGS_PACKED_ENCODING_BIT_WIDTH) {
                let (of, eq, gt) = integer_into_flags(i as u8);
                let resolution = match condition {
                    Condition::Always => true,
                    Condition::Lt => of,
                    Condition::Eq => eq,
                    Condition::Gt => gt,
                    Condition::Ge => gt || eq,
                    Condition::Le => of || eq,
                    Condition::Ne => !eq,
                    Condition::GtOrLt => gt || of,
                };
                let x_fr = u64_to_fe(x as u64);
                let y_fr = u64_to_fe(i as u64);
                let z_fr = u64_to_fe(resolution as u64);

                key_0.push(x_fr);
                key_1.push(y_fr);
                value.push(z_fr);
                let existing = map.insert((x_fr, y_fr), z_fr);
                assert!(existing.is_none());
            }
        }

        assert_eq!(key_0.len(), num_rows);

        Self {
            table_entries: [key_0, key_1, value],
            table_lookup_map: map,
            table_size: num_rows,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for ConditionalResolutionTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConditionalResolutionTable").finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for ConditionalResolutionTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        self.table_size
    }
    fn num_keys(&self) -> usize {
        2
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![
            self.table_entries[0].clone(),
            self.table_entries[1].clone(),
            self.table_entries[2].clone(),
        ]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &values[0];
        }
        false
    }

    #[track_caller]
    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry]);
        }

        panic!("Invalid input into table {}: {:?}", self.name(), keys);
        // Err(SynthesisError::Unsatisfiable)
    }
}
