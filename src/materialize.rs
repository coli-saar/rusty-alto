use crate::{Arity, BottomUpTa, Explicit, Interner, Memo, StateId, Symbol, run::cartesian_product};
use fixedbitset::FixedBitSet;

/// Explore a finite automaton and return an equivalent explicit fragment.
///
/// `materialize` starts from all nullary symbols in `alphabet`, repeatedly
/// queries transitions over already discovered states, and freezes every
/// queried rule into an [`Explicit`] automaton. The returned [`Interner`] maps
/// the explicit [`StateId`] values back to the original state type.
///
/// The caller must provide a finite alphabet as `(symbol, arity)` pairs. The
/// construction terminates when the reachable state space is finite. If the
/// implicit automaton can keep producing fresh states forever, this function
/// will also keep exploring.
///
/// Arity 0, 1, and 2 are handled directly. Higher arities are supported but can
/// be expensive because the number of state tuples grows exponentially.
pub fn materialize<A: BottomUpTa>(
    a: &A,
    alphabet: &[(Symbol, Arity)],
) -> (Explicit, Interner<A::State>) {
    let memo = Memo::new(a);
    let mut known = Vec::<StateId>::new();
    let mut known_bits = FixedBitSet::new();
    let mut worklist = Vec::<StateId>::new();

    for &(symbol, arity) in alphabet {
        if arity == 0 {
            collect_step(
                &memo,
                symbol,
                &[],
                &mut known,
                &mut known_bits,
                &mut worklist,
            );
        }
    }

    while let Some(popped) = worklist.pop() {
        let snapshot = known.clone();
        for &(symbol, arity) in alphabet {
            match arity {
                0 => {}
                1 => collect_step(
                    &memo,
                    symbol,
                    &[popped],
                    &mut known,
                    &mut known_bits,
                    &mut worklist,
                ),
                2 => {
                    for &other in &snapshot {
                        collect_step(
                            &memo,
                            symbol,
                            &[popped, other],
                            &mut known,
                            &mut known_bits,
                            &mut worklist,
                        );
                        if other != popped {
                            collect_step(
                                &memo,
                                symbol,
                                &[other, popped],
                                &mut known,
                                &mut known_bits,
                                &mut worklist,
                            );
                        }
                    }
                }
                n => {
                    let pools = vec![snapshot.as_slice(); n as usize];
                    cartesian_product(&pools, |tuple| {
                        if tuple.contains(&popped) {
                            collect_step(
                                &memo,
                                symbol,
                                tuple,
                                &mut known,
                                &mut known_bits,
                                &mut worklist,
                            );
                        }
                    });
                }
            }
        }
    }

    memo.into_explicit()
}

fn collect_step<A: BottomUpTa>(
    memo: &Memo<&A>,
    symbol: Symbol,
    children: &[StateId],
    known: &mut Vec<StateId>,
    known_bits: &mut FixedBitSet,
    worklist: &mut Vec<StateId>,
) {
    memo.step(symbol, children, &mut |q| {
        if !known_bits.contains(q.index()) {
            known_bits.grow(q.index() + 1);
            known_bits.set(q.index(), true);
            known.push(q);
            worklist.push(q);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BottomUpTa, ExplicitBuilder};

    #[test]
    fn materializes_explicit_identity_fragment() {
        let a = Symbol(0);
        let f = Symbol(1);
        let mut b = ExplicitBuilder::new();
        let leaf = b.new_state();
        let root = b.new_state();
        b.add_rule(a, vec![], leaf);
        b.add_rule(f, vec![leaf, leaf], root);
        b.add_accepting(root);
        let explicit = b.build();

        let (mat, _interner) = materialize(&explicit, &[(a, 0), (f, 2)]);
        let mut leaves = Vec::new();
        mat.step(a, &[], &mut |q| leaves.push(q));
        let mut roots = Vec::new();
        mat.step(f, &[leaves[0], leaves[0]], &mut |q| roots.push(q));
        assert_eq!(roots.len(), 1);
        assert!(mat.is_accepting(&roots[0]));
    }
}
