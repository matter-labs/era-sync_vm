use super::*;

#[derive(Clone)]
pub struct ShiftToNumConverter<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    is_low: bool,
    name: &'static str,
}

impl<E: Engine> ShiftToNumConverter<E> {
    pub fn new(name: &'static str, is_low: bool) -> Self {
        let num_rows: usize = 256;

        let mut key = Vec::with_capacity(num_rows);
        let mut value_0 = Vec::with_capacity(num_rows);
        let mut value_1 = Vec::with_capacity(num_rows);
        let mut map = std::collections::HashMap::with_capacity(num_rows);

        let get_limb = |shift: u64, limb_idx: u64| -> u64 {
            let modulus = BigUint::from(1u64) << shift;
            let limbs = modulus.iter_u64_digits().collect::<Vec<u64>>();
            limbs.get(limb_idx as usize).cloned().unwrap_or_default()
        };

        for x in 0..num_rows {
            let y_idx = if is_low { 0 } else { 2 };
            let z_idx = if is_low { 1 } else { 3 };

            let y = get_limb(x as u64, y_idx);
            let z = get_limb(x as u64, z_idx);

            let x = u64_to_fe(x as u64);
            let y = u64_to_fe(y);
            let z = u64_to_fe(z);

            key.push(x);
            value_0.push(y);
            value_1.push(z);

            map.insert(x, (y, z));
        }

        Self {
            table_entries: [key, value_0, value_1],
            table_lookup_map: map,
            is_low,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for ShiftToNumConverter<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ShiftToNumConverter")
            .field("is_low", &self.is_low)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for ShiftToNumConverter<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        256
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
