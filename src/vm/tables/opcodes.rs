use super::*;

use num_traits::FromPrimitive;

// first column contain the opcodes' integer encoding
// second column contains their corresponding price in ergs
// third column contains a number than bit a special bitmask of opcode properties
#[derive(Clone)]
pub struct OpcodeDecodingTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    name: &'static str,
    table_size: usize,
}

impl<E: Engine> OpcodeDecodingTable<E> {
    pub fn new(name: &'static str) -> Self {
        let num_rows = zkevm_opcode_defs::OPCODES_TABLE.len();
        let mut key = Vec::with_capacity(num_rows);
        let mut value_0 = Vec::with_capacity(num_rows);
        let mut value_1 = Vec::with_capacity(num_rows);
        let mut map = std::collections::HashMap::with_capacity(num_rows);

        for x in 0..num_rows {
            let opcode_as_integer = x as u64;
            let opcode_props_encoding = zkevm_opcode_defs::OPCODES_PROPS_INTEGER_BITMASKS[x];
            let price = zkevm_opcode_defs::OPCODES_PRICES[x];

            let x_fr = u64_to_fe(opcode_as_integer);
            let y_fr = u64_to_fe(price as u64);
            let z_fr = u64_to_fe(opcode_props_encoding as u64);

            key.push(x_fr);
            value_0.push(y_fr);
            value_1.push(z_fr);
            map.insert(x_fr, (y_fr, z_fr));
        }

        Self {
            table_entries: [key, value_0, value_1],
            table_lookup_map: map,
            table_size: num_rows,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for OpcodeDecodingTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpcodeDecodingTable").finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for OpcodeDecodingTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        self.table_size
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        2
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

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    #[track_caller]
    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1]);
        }

        panic!("Invalid input into table {}: {:?}", self.name(), keys);
        // Err(SynthesisError::Unsatisfiable)
    }
}
