use super::*;
use crate::bellman::plonk::better_better_cs::cs::*;
use crate::vm::ports::ArithmeticFlagsPort;
use crate::vm::primitives::register_view::*;
use franklin_crypto::bellman::plonk::better_better_cs::cs::LookupTableApplication;
use itertools::Itertools;
use std::sync::Arc;

fn apply_table<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    table: Arc<LookupTableApplication<E>>,
    vars: &[Variable],
    selectors: &[E::Fr],
) -> Result<(), SynthesisError> {
    let gate_term = MainGateTerm::new();
    let dummy = AllocatedNum::zero(cs).get_variable();
    let (mut gate_vars, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
    gate_vars.copy_from_slice(vars);

    let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
    let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
    let idx_of_last_linear_term = range_of_next_step_linear_terms
        .last()
        .expect("must have an index");
    let (next_step_sel, linear_selectors) = selectors.split_last().unwrap();

    gate_coefs[range_of_linear_terms].copy_from_slice(linear_selectors);
    gate_coefs[idx_of_last_linear_term] = next_step_sel.clone();

    cs.begin_gates_batch_for_step()?;
    cs.apply_single_lookup_gate(&gate_vars[..table.width()], table.clone())?;
    cs.new_gate_in_batch(&CS::MainGate::default(), &gate_coefs, &gate_vars, &[])?;
    cs.end_gates_batch_for_step()?;

    Ok(())
}

pub(crate) fn apply<
    E: Engine,
    CS: ConstraintSystem<E>,
    R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
>(
    cs: &mut CS,
    _current_state: &VmLocalState<E, 3>,
    common_opcode_state: &CommonOpcodeState<E>,
    _opcode_carry_parts: &OpcodeCarryParts<E>,
    _global_context: &GlobalContext<E>,
    optimizer: &mut OptimizationContext<E>,
    _round_function: &R,
    _witness_oracle: &mut impl WitnessOracle<E>,
) -> Result<OpcodePartialApplicationResult<E, PropsMarker>, SynthesisError> {
    let n = cs.get_current_aux_gate_number();

    let and_opcode =
        zkevm_opcode_defs::Opcode::Binop(zkevm_opcode_defs::definitions::binop::BinopOpcode::And);
    let or_opcode =
        zkevm_opcode_defs::Opcode::Binop(zkevm_opcode_defs::definitions::binop::BinopOpcode::Or);
    let xor_opcode =
        zkevm_opcode_defs::Opcode::Binop(zkevm_opcode_defs::definitions::binop::BinopOpcode::Xor);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(and_opcode);

    let should_set_flags = common_opcode_state
        .decoded_opcode
        .properties_bits
        .flag_booleans[SET_FLAGS_FLAG_IDX];
    let marker = CtxMarker::from(and_opcode);
    let shifts = compute_shifts::<E::Fr>();

    let is_and = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(and_opcode);
    let is_or = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(or_opcode);
    let is_xor = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_variant(xor_opcode);

    if crate::VERBOSE_CIRCUITS && should_apply.get_value().unwrap_or(false) {
        if is_and.get_value().unwrap_or(false) {
            println!("Executing BINOP AND");
        }
        if is_or.get_value().unwrap_or(false) {
            println!("Executing BINOP OR");
        }
        if is_xor.get_value().unwrap_or(false) {
            println!("Executing BINOP XOR");
        }
    }

    let src0_limbs = &common_opcode_state.src0_view.u8x32_view.unwrap();
    let src1_limbs = &common_opcode_state.src1_view.u8x32_view.unwrap();

    let table = cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME)?;
    // set of 32 arrays where each array is 1 byte from the binop over them
    let mut output_limbs = [[Num::zero(); 3]; 32];

    let zipped_iter = (
        src0_limbs.iter(),
        src1_limbs.iter(),
        output_limbs.iter_mut(),
    );
    for (limb_in0, limb_in1, limb_out) in itertools::multizip(zipped_iter) {
        let (and_chunk, or_chunk, xor_chunk) = match (limb_in0.inner, limb_in1.inner) {
            (Num::Variable(var0), Num::Variable(var1)) => {
                let wrapped_val0 = var0.get_value();
                let wrapped_val1 = var1.get_value();
                let full_val = if wrapped_val0.is_some() && wrapped_val1.is_some() {
                    let out_val = table.query(&[wrapped_val0.unwrap(), wrapped_val1.unwrap()])?;
                    Some(out_val[0])
                } else {
                    None
                };

                let chunks_vals = full_val.map_or([None; 4], |fr| {
                    let el = fe_to_u64(fr);
                    let mask = (1u64 << 8) - 1;
                    let l0 = u64_to_fe::<E::Fr>(el & mask);
                    let l1 = u64_to_fe::<E::Fr>((el >> 16) & mask);
                    let l2 = u64_to_fe::<E::Fr>((el >> 32) & mask);
                    let l3 = u64_to_fe::<E::Fr>((el >> 16) << 16);

                    [Some(l0), Some(l1), Some(l2), Some(l3)]
                });

                let full = AllocatedNum::alloc(cs, || full_val.grab())?;
                let and = AllocatedNum::alloc(cs, || chunks_vals[0].grab())?;
                let or = AllocatedNum::alloc(cs, || chunks_vals[1].grab())?;
                let xor = AllocatedNum::alloc(cs, || chunks_vals[2].grab())?;
                let tmp = AllocatedNum::alloc(cs, || chunks_vals[3].grab())?;
                let unused_val = match (or.get_value(), xor.get_value()) {
                    (Some(or), Some(xor)) => {
                        let out_val = table.query(&[or, xor])?;

                        Some(out_val[0])
                    }
                    _ => None,
                };
                let unused = AllocatedNum::alloc(cs, || Ok(unused_val.grab()?))?;

                let zero = E::Fr::zero();
                let one = E::Fr::one();
                let mut minus_one = one.clone();
                minus_one.negate();

                // we could retrieve and, or and xored chunks with two gates only as follows:
                // note that table full_res = and_res + or_res << 16 + xor_res << 32
                // and let tmp = full_res - and_res
                // the first row would be: (op0, op1, full_res, and_res)
                // the second row would be: (or_res, xor_res, unused, tmp)
                // we apply and/or/xor table on both rows
                // additional polynomial constraints would be:
                // c - d - d_next = 0 on the first row
                // and a * 2^16 + b * 2^32 - tmp = 0
                let vars = [
                    var0.get_variable(),
                    var1.get_variable(),
                    full.get_variable(),
                    and.get_variable(),
                ];
                let sels = [
                    zero.clone(),
                    zero.clone(),
                    one.clone(),
                    minus_one.clone(),
                    minus_one.clone(),
                ];
                apply_table(cs, table.clone(), &vars[..], &sels[..])?;
                let vars = [
                    or.get_variable(),
                    xor.get_variable(),
                    unused.get_variable(),
                    tmp.get_variable(),
                ];
                let sels = [
                    shifts[16].clone(),
                    shifts[32].clone(),
                    zero.clone(),
                    minus_one,
                    zero,
                ];
                apply_table(cs, table.clone(), &vars[..], &sels[..])?;

                let res_and = Num::Variable(and);
                let res_or = Num::Variable(or);
                let res_xor = Num::Variable(xor);
                (res_and, res_or, res_xor)
            }
            _ => unreachable!(),
        };

        *limb_out = [and_chunk, or_chunk, xor_chunk];
    }

    let shifts = compute_shifts::<E::Fr>();

    let mut out_candidates = [
        [
            LinearCombination::zero(),
            LinearCombination::zero(),
            LinearCombination::zero(),
        ],
        [
            LinearCombination::zero(),
            LinearCombination::zero(),
            LinearCombination::zero(),
        ],
    ];

    // take chunks of 16 bytes and form linear combinations
    for (dst, src_set) in out_candidates.iter_mut().zip(output_limbs.chunks(16)) {
        let mut shift = 0;

        for src in src_set.iter() {
            for (dst, src) in dst.iter_mut().zip(src.iter()) {
                dst.add_assign_number_with_coeff(src, shifts[shift]);
            }
            shift += 8;
        }
        assert!(shift <= E::Fr::CAPACITY as usize);
    }

    // now we have chunks that encode each result as UInt128, collapse linear combinations and select over them
    let mut output_chunks = [UInt128::zero(); 2];
    for (src, dst) in out_candidates.into_iter().zip(output_chunks.iter_mut()) {
        let [and_lc, or_lc, xor_lc] = src;
        let and_num = and_lc.into_num(cs)?;
        let or_num = or_lc.into_num(cs)?;
        let xor_num = xor_lc.into_num(cs)?;

        let mut res = and_num;
        for (flag, value) in [(is_or, or_num), (is_xor, xor_num)].iter() {
            res = Num::conditionally_select(cs, flag, value, &res)?;
        }

        *dst = UInt128::from_num_unchecked(res);
    }

    let register = Register {
        inner: output_chunks,
        is_ptr: Boolean::Constant(false),
    };

    // Sets an eq flag if out is zero
    let eq = optimizer.add_zero_check(cs, &register, should_apply, marker)?;
    let new_flag_port = ArithmeticFlagsPort::<E> {
        overflow_or_less_than: Boolean::constant(false),
        equal: eq,
        greater_than: Boolean::constant(false),
        _marker: std::marker::PhantomData::<E>,
    };

    let mut opcode_partial_application = OpcodePartialApplicationResult::default();
    opcode_partial_application.marker = PropsMarker::Normal(and_opcode);
    opcode_partial_application.applies = should_apply;
    opcode_partial_application.dst0_value = Some((should_apply, register));

    // let original_flags = common_opcode_state.current_flags;
    // let preserve_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags.not()])?;
    // opcode_partial_application.flags.push((preserve_flags_and_execute, original_flags));

    // flags for a case if we do not set flags
    let set_flags_and_execute = smart_and(cs, &[should_apply, should_set_flags])?;
    opcode_partial_application
        .flags
        .push((set_flags_and_execute, new_flag_port));

    let gates_used = cs.get_current_aux_gate_number() - n;
    let _message = format!("{} gates used for opcode {:?}", gates_used, and_opcode);
    // dbg!(_message);

    Ok(opcode_partial_application)
}
