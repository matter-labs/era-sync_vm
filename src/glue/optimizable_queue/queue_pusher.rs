use super::*;
use crate::vm::primitives::*;
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct PushRequest<
    E: Engine,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
> {
    pub item: I,
    pub execute: Boolean,
    pub(crate) _marker: std::marker::PhantomData<E>,
}

pub struct QueuePushOptimizer<
    E: Engine,
    I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
    const N: usize,
> {
    pub(crate) requests: std::collections::HashMap<u64, Vec<PushRequest<E, I, N>>>,
    pub(crate) limit: usize,
    pub(crate) _marker: std::marker::PhantomData<E>,
}

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    > QueuePushOptimizer<E, I, N>
{
    pub fn new(limit: usize) -> Self {
        Self {
            requests: std::collections::HashMap::new(),
            limit,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn capacity(&self) -> usize {
        self.limit
    }

    pub fn add_request(&mut self, item: I, applies: Boolean, id: u64) {
        let request = PushRequest {
            item,
            execute: applies,
            _marker: std::marker::PhantomData,
        };

        if let Some(existing_vector) = self.requests.get_mut(&id) {
            assert!(existing_vector.len() < self.limit, "over capacity");
            existing_vector.push(request);
        } else {
            let vector = vec![request];
            self.requests.insert(id, vector);
        }
    }

    pub fn get_pushed_witness(&self) -> Option<Vec<I>> {
        let mut layout = vec![];
        let mut keys: Vec<_> = self.requests.keys().cloned().collect();
        let mut requests = self.requests.clone();
        keys.sort();
        for _ in 0..self.limit {
            let mut per_round_requests = vec![];
            for k in keys.iter() {
                let requests_per_id = requests.get_mut(k).expect("is some");
                if requests_per_id.len() > 0 {
                    if let Some(el) = requests_per_id.drain(0..1).next() {
                        per_round_requests.push(el);
                    }
                }
            }

            let mut selected_item = None;
            let mut applicability_flags = vec![];
            let it = per_round_requests.into_iter();
            for req in it {
                let PushRequest { item, execute, .. } = req;
                if execute.get_value()? {
                    selected_item = Some(item);
                }
                applicability_flags.push(execute);
            }

            // this is kind of debug assert
            let mut encountered_true = false;
            for f in applicability_flags.iter() {
                if let Some(f) = f.get_value() {
                    if f {
                        if encountered_true {
                            panic!("not exclusive branches in optimizer")
                        } else {
                            encountered_true = true;
                        }
                    }
                }
            }

            if let Some(item) = selected_item {
                layout.push(item);
            }
        }

        Some(layout)
    }

    pub fn place_into_queue<
        CS: ConstraintSystem<E>,
        R: CircuitArithmeticRoundFunction<E, AWIDTH, SWIDTH, StateElement = Num<E>>,
        const AWIDTH: usize,
        const SWIDTH: usize,
    >(
        &mut self,
        cs: &mut CS,
        queue: &mut FixedWidthEncodingGenericQueue<E, I, N>,
        round_function: &R,
    ) -> Result<(), SynthesisError> {
        let mut layout = vec![];
        let mut keys: Vec<_> = self.requests.keys().cloned().collect();
        keys.sort();
        for _ in 0..self.limit {
            let mut per_round_requests = vec![];
            for k in keys.iter() {
                let requests_per_id = self.requests.get_mut(k).expect("is some");
                if requests_per_id.len() > 0 {
                    if let Some(el) = requests_per_id.drain(0..1).next() {
                        per_round_requests.push(el);
                    }
                }
            }

            let len = per_round_requests.len();
            if len > 1 {
                let mut applicability_flags = vec![];
                let mut it = per_round_requests.into_iter();
                let PushRequest { item, execute, .. } = (&mut it).next().expect("is some");
                let mut item_wit = item.create_witness();
                let mut encoding = item.encode(cs)?;
                applicability_flags.push(execute);
                for req in it {
                    let PushRequest { item, execute, .. } = req;
                    let new_encoding = item.encode(cs)?;
                    encoding = <[Num<E>; N]>::conditionally_select(
                        cs,
                        &execute,
                        &new_encoding,
                        &encoding,
                    )?;
                    applicability_flags.push(execute);
                    if execute.get_value().unwrap_or(false) {
                        item_wit = item.create_witness();
                    }
                }

                // this is kind of debug assert
                let mut encountered_true = false;
                for f in applicability_flags.iter() {
                    if let Some(f) = f.get_value() {
                        if f {
                            if encountered_true {
                                panic!("not exclusive branches in optimizer")
                            } else {
                                encountered_true = true;
                            }
                        }
                    }
                }

                // we would potentially ensure that we only have a single boolean in the vector here,
                // but it's not necessary for all our use cases where we use this optimizer for orthogonal branches
                let applies = smart_or(cs, &applicability_flags)?;
                layout.push((encoding, applies, item_wit));
            } else if len == 1 {
                let PushRequest { item, execute, .. } =
                    per_round_requests.drain(0..1).next().expect("is some");
                let item_wit = item.create_witness();
                let encoding = item.encode(cs)?;
                layout.push((encoding, execute, item_wit));
            }
        }
        self.requests.clear();

        assert!(layout.len() <= self.limit);
        for (encoding, execute, witness) in layout.into_iter() {
            queue.push_raw(cs, encoding, witness, &execute, round_function)?;
        }

        Ok(())
    }
}

impl<
        E: Engine,
        I: CircuitFixedLengthEncodableExt<E, N> + CircuitFixedLengthDecodableExt<E, N>,
        const N: usize,
    > Drop for QueuePushOptimizer<E, I, N>
{
    fn drop(&mut self) {
        assert!(self.requests.is_empty(), "requests were not enforced!");
    }
}
