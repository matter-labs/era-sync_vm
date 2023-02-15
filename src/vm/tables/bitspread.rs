use super::*;

// second row contains corresponding bit decomposition;
// third row contains boolean flag indicating if value if out of bounds
#[derive(Clone)]
pub struct NumToBitmaskConverter<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    max_num: u64,
    num_rows: usize,
    name: &'static str,
}

impl<E: Engine> NumToBitmaskConverter<E> {
    pub fn new(name: &'static str, max_num: u64) -> Self {
        let num_rows = (max_num + 1).next_power_of_two() as usize;

        let mut key = Vec::with_capacity(num_rows);
        let mut value_0 = Vec::with_capacity(num_rows);
        let mut value_1 = Vec::with_capacity(num_rows);
        let mut map = std::collections::HashMap::with_capacity(num_rows);
        let max_num_usize = max_num as usize;

        for x in 0..num_rows {
            let y = if x == 0 || x > max_num_usize {
                0
            } else {
                1 << (x - 1)
            };

            let x_fr = u64_to_fe(x as u64);
            let y_fr = u64_to_fe(y as u64);
            let z_fr = if x <= max_num_usize {
                E::Fr::zero()
            } else {
                E::Fr::one()
            };

            key.push(x_fr);
            value_0.push(y_fr);
            value_1.push(z_fr);

            map.insert(x_fr, (y_fr, z_fr));
        }

        Self {
            table_entries: [key, value_0, value_1],
            table_lookup_map: map,
            max_num,
            num_rows,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for NumToBitmaskConverter<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NumToBitmaskConverter")
            .field("max_num", &self.max_num)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for NumToBitmaskConverter<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        self.num_rows
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
