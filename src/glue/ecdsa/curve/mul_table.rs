use super::*;
use super::readonly_table::*;
use franklin_crypto::plonk::circuit::bigint::*;
use franklin_crypto::plonk::circuit::curve::*;

use std::convert::TryInto;

pub struct MulTable<'a, E: Engine, G: GenericCurveAffine, const N: usize> where G::Base: PrimeField {
    pub window_width: usize,
    read_only_table: ReadOnlyTable<E, N>,
    _marker: std::marker::PhantomData<&'a G>
}

impl<'a, E: Engine, G: GenericCurveAffine, const N: usize> MulTable<'a, E, G, N> where G::Base: PrimeField {
    fn new_up_to_power_for_fixed_point(
        base_point: G, 
        power: usize, 
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        assert!(power >= 3);
        let mut kvs = vec![];
        // special case of key == 0 - just use some random point and subtract later
        let random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log_generic::<G::Projective>(b"WMUL_DST", 1)[0];

        let key = UInt16::<E>::zero();
        let p = AffinePoint::constant(random_point, rns_params);
        let values: Vec<Num<E>> = p.x.binary_limbs.iter().chain(p.y.binary_limbs.iter()).map(|el| el.term.into_num()).collect();
        let values: [Num<E>; N] = values[..].try_into().expect("length must match");

        kvs.push((key, values));

        let mut point = base_point.into_projective();

        for i in 1..=power {
            let p = point.into_affine();

            let key = UInt16::<E>::from_uint(i as u16);
            let p = AffinePoint::constant(p, rns_params);
            let values: Vec<Num<E>> = p.x.binary_limbs.iter().chain(p.y.binary_limbs.iter()).map(|el| el.term.into_num()).collect();
            let values: [Num<E>; N] = values[..].try_into().expect("length must match");
            kvs.push((key, values));

            point.add_assign_mixed(&base_point);
        }

        let mut parameters: [Option<usize>; N] = [None; N];

        let mut it = rns_params.binary_limbs_bit_widths.iter().chain(rns_params.binary_limbs_bit_widths.iter());
        
        for i in 0..N {
            let width = (&mut it).next().expect("is some");
            parameters[i] = Some(*width);
        }

        assert!(it.next().is_none());

        let mut table = ReadOnlyTable::new_for_range_parameters(parameters);
        table.place_initial_values(&kvs);

        Self {
            window_width: power.trailing_zeros() as usize,
            read_only_table: table,
            _marker: std::marker::PhantomData
        }
    }
    pub fn new_for_fixed_point(
        base_point: G, 
        scalar_window_width: usize, 
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        let mut new = Self::new_up_to_power_for_fixed_point(
            base_point, 
            (1 << scalar_window_width) - 1,
            rns_params
        );
        new.window_width = scalar_window_width;

        new
    }  

    pub fn new_signed_for_fixed_point(
        base_point: G, 
        scalar_window_width: usize, 
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Self {
        let mut new = Self::new_up_to_power_for_fixed_point(
            base_point, 
            1 << (scalar_window_width-1),
            rns_params
        );
        new.window_width = scalar_window_width;

        new
    }  

    fn new_up_to_power_for_variable_point<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        base_point: AffinePoint<'a, E, G>,
        power: usize,
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        assert!(power >= 3);
        let mut kvs = vec![];
        // special case of key == 0 - just use some random point and subtract later
        let random_point = franklin_crypto::constants::make_random_points_with_unknown_discrete_log_generic::<G::Projective>(b"WMUL_DST", 1)[0];

        let key = UInt16::<E>::from_uint(0);
        let p = AffinePoint::constant(random_point, rns_params);
        let values: Vec<Num<E>> = p.x.binary_limbs.iter().chain(p.y.binary_limbs.iter()).map(|el| el.term.into_num()).collect();
        let values: [Num<E>; N] = values[..].try_into().expect("length must match");

        kvs.push((key, values));

        let mut point = base_point.clone();
        // point itself
        {
            let key = UInt16::<E>::from_uint(1u16);
            let p = point;
            let values: Vec<Num<E>> = p.x.binary_limbs.iter().chain(p.y.binary_limbs.iter()).map(|el| el.term.into_num()).collect();
            let values: [Num<E>; N] = values[..].try_into().expect("length must match");
            kvs.push((key, values));

            point = p;
        }

        // manual doubling 
        {
            let key = UInt16::<E>::from_uint(2u16);
            let (p, _) = point.double(cs)?;
            let values: Vec<Num<E>> = p.x.binary_limbs.iter().chain(p.y.binary_limbs.iter()).map(|el| el.term.into_num()).collect();
            let values: [Num<E>; N] = values[..].try_into().expect("length must match");
            kvs.push((key, values));

            point = p;
        }

        for i in 3..=power {
            let key = UInt16::<E>::from_uint(i as u16);
            let (p, _) = point.add_unequal_unchecked(cs, base_point.clone())?;
            let values: Vec<Num<E>> = p.x.binary_limbs.iter().chain(p.y.binary_limbs.iter()).map(|el| el.term.into_num()).collect();
            let values: [Num<E>; N] = values[..].try_into().expect("length must match");
            kvs.push((key, values));

            point = p;
        }

        let mut parameters: [Option<usize>; N] = [None; N];

        let mut it = rns_params.binary_limbs_bit_widths.iter().chain(rns_params.binary_limbs_bit_widths.iter());
        
        for i in 0..N {
            let width = (&mut it).next().expect("is some");
            parameters[i] = Some(*width);
        }

        assert!(it.next().is_none());

        let mut table = ReadOnlyTable::new_for_range_parameters(parameters);
        table.place_initial_values(&kvs);

        let table = Self {
            window_width: power.trailing_zeros() as usize,
            read_only_table: table,
            _marker: std::marker::PhantomData
        };

        Ok(table)
    }

    pub fn new_for_variable_point<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        base_point: AffinePoint<'a, E, G>,
        scalar_window_width: usize,
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::new_up_to_power_for_variable_point(
            cs, 
            base_point, 
            (1 << scalar_window_width) - 1,
            rns_params
        )?;
        new.window_width = scalar_window_width;

        Ok(new)
    }

    pub fn new_signed_for_variable_point<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        base_point: AffinePoint<'a, E, G>,
        scalar_window_width: usize, 
        rns_params: &'a RnsParameters<E, G::Base>
    ) -> Result<Self, SynthesisError> {
        let mut new = Self::new_up_to_power_for_variable_point(
            cs, 
            base_point, 
            1 << (scalar_window_width - 1),
            rns_params
        )?;
        new.window_width = scalar_window_width;

        Ok(new)
    }  

    #[track_caller]
    pub fn read<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, at: UInt16<E>) -> Result<[Num<E>; N], SynthesisError> {
        self.read_only_table.read(cs, at)
    }

    pub fn enforce_validity_optimized<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.read_only_table.enforce_validity_optimized(cs)
    }
} 