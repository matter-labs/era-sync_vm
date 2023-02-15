use super::*;

#[derive(Clone)]
pub struct BitwiseLogicTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    name: &'static str,
}

impl<E: Engine> BitwiseLogicTable<E> {
    pub fn new(name: &'static str, bits: usize) -> Self {
        let table_len = 1 << (2 * bits);
        let var_range = 1 << bits;

        let mut keys0 = Vec::with_capacity(table_len);
        let mut keys1 = Vec::with_capacity(table_len);
        let mut values = Vec::with_capacity(table_len);
        let mut map = std::collections::HashMap::with_capacity(table_len);

        for (x, y) in (0..var_range).cartesian_product(0..var_range) {
            let res_and = (x & y) as u64;
            let res_or = (x | y) as u64;
            let res_xor = (x ^ y) as u64;
            let z = res_and + (res_or << 16) + (res_xor << 32);

            let x = u64_to_fe(x as u64);
            let y = u64_to_fe(y as u64);
            let z = u64_to_fe(z as u64);

            keys0.push(x);
            keys1.push(y);
            values.push(z);
            map.insert((x, y), z);
        }

        Self {
            table_entries: [keys0, keys1, values],
            table_lookup_map: map,
            bits,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for BitwiseLogicTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitwiseLogicTable")
            .field("bits", &self.bits)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for BitwiseLogicTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
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
        assert!(column_num <= 2);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
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
