use crate::{
    BottomUpTa, DetBottomUpTa, FxHashMap, FxHashSet, Symbol,
    homomorphism::{HomLabel, HomTerm, Homomorphism},
    run::cartesian_product,
    traits::{CondensedTa, CondensedTopDownTa, StateUniverse, SymbolSet, TopDownTa},
};
use packed_term_arena::tree::TreeArena;
use smallvec::SmallVec;

/// Nondeleting inverse-homomorphism automaton.
///
/// `InvHom<A>` accepts a source tree `t` exactly when the wrapped automaton
/// `A` accepts the homomorphic image `h(t)`. The state type is unchanged: a
/// source subtree receives the state that `A` assigns to its image.
///
/// The homomorphism is validated when it is built, so every source child occurs
/// exactly once in each image term. This gives the condensed implementation a
/// well-defined way to recover source child states from target-side rules.
pub struct InvHom<'h, A> {
    inner: A,
    hom: &'h Homomorphism,
}

impl<'h, A> InvHom<'h, A> {
    /// Wrap `inner` with the given homomorphism.
    pub fn new(inner: A, hom: &'h Homomorphism) -> Self {
        Self { inner, hom }
    }

    /// Return the wrapped automaton.
    pub fn inner(&self) -> &A {
        &self.inner
    }

    /// Return the homomorphism used to map source symbols to target terms.
    pub fn homomorphism(&self) -> &Homomorphism {
        self.hom
    }
}

fn eval_term<A: BottomUpTa>(
    arena: &TreeArena<HomLabel>,
    term: HomTerm,
    src_children: &[A::State],
    inner: &A,
    out: &mut dyn FnMut(A::State),
) {
    match *arena.get_label(term) {
        HomLabel::Var(i) => {
            if let Some(q) = src_children.get(i) {
                out(q.clone());
            }
        }
        HomLabel::Symbol(symbol) => {
            let term_children = arena.get_children(term);
            if term_children.is_empty() {
                inner.step(symbol, &[], out);
                return;
            }

            let mut child_states: SmallVec<[SmallVec<[A::State; 2]>; 4]> = SmallVec::new();
            for &child in term_children {
                let mut states = SmallVec::new();
                eval_term(arena, child, src_children, inner, &mut |q| states.push(q));
                if states.is_empty() {
                    return;
                }
                child_states.push(states);
            }

            let slices: SmallVec<[&[A::State]; 4]> = child_states
                .iter()
                .map(|states| states.as_slice())
                .collect();
            cartesian_product(&slices, |combo| inner.step(symbol, combo, out));
        }
    }
}

fn eval_term_det<A: DetBottomUpTa>(
    arena: &TreeArena<HomLabel>,
    term: HomTerm,
    src_children: &[A::State],
    inner: &A,
) -> Option<A::State> {
    match *arena.get_label(term) {
        HomLabel::Var(i) => src_children.get(i).cloned(),
        HomLabel::Symbol(symbol) => {
            let mut combo = SmallVec::<[A::State; 4]>::new();
            for &child in arena.get_children(term) {
                combo.push(eval_term_det(arena, child, src_children, inner)?);
            }
            inner.step_det(symbol, &combo)
        }
    }
}

impl<A: BottomUpTa> BottomUpTa for InvHom<'_, A> {
    type State = A::State;

    fn step(&self, f_src: Symbol, children: &[A::State], out: &mut dyn FnMut(A::State)) {
        let Some(term) = self.hom.get(f_src) else {
            return;
        };

        let mut seen = FxHashSet::default();
        eval_term(self.hom.arena(), term, children, &self.inner, &mut |q| {
            if seen.insert(q.clone()) {
                out(q);
            }
        });
    }

    fn is_accepting(&self, q: &A::State) -> bool {
        self.inner.is_accepting(q)
    }
}

impl<A: DetBottomUpTa> DetBottomUpTa for InvHom<'_, A> {
    fn step_det(&self, f_src: Symbol, children: &[A::State]) -> Option<A::State> {
        let term = self.hom.get(f_src)?;
        eval_term_det(self.hom.arena(), term, children, &self.inner)
    }

    /// Source symbols sharing an image term yield identical `step_det` results
    /// for any given children, so the structurally-deduplicated term id groups
    /// them: callers can compute one transition per group and reuse it for every
    /// symbol in the set. Unmapped symbols (`step_det` is always `None`) map to a
    /// sentinel group.
    fn det_group(&self, f_src: Symbol) -> u32 {
        self.hom.term_id(f_src).map_or(u32::MAX, |tid| tid as u32)
    }
}

impl<A: StateUniverse> StateUniverse for InvHom<'_, A> {
    fn all_states(&self, out: &mut dyn FnMut(A::State)) {
        self.inner.all_states(out);
    }
}

#[derive(Clone, Debug)]
struct InnerCondensedRule<S> {
    children: Vec<S>,
    symbols: SymbolSet,
    result: S,
}

#[derive(Clone, Debug)]
struct PartialEval<S> {
    assignments: Vec<Option<S>>,
    result: S,
}

#[derive(Clone, Debug)]
struct DirectTerm {
    symbol: Symbol,
    variables: Vec<usize>,
}

fn direct_linear_term(
    arena: &TreeArena<HomLabel>,
    term: HomTerm,
    arity: usize,
) -> Option<DirectTerm> {
    let HomLabel::Symbol(symbol) = *arena.get_label(term) else {
        return None;
    };

    let mut seen = vec![false; arity];
    let mut variables = Vec::new();
    for &child in arena.get_children(term) {
        let HomLabel::Var(variable) = *arena.get_label(child) else {
            return None;
        };
        if variable >= arity || seen[variable] {
            return None;
        }
        seen[variable] = true;
        variables.push(variable);
    }

    Some(DirectTerm { symbol, variables })
}

#[allow(clippy::type_complexity)]
fn match_topdown_term<A>(
    arena: &TreeArena<HomLabel>,
    term: HomTerm,
    state: &A::State,
    arity: usize,
    inner: &A,
    subst: &mut [Option<A::State>],
    out: &mut dyn FnMut(&mut [Option<A::State>]),
) where
    A: TopDownTa,
{
    match *arena.get_label(term) {
        HomLabel::Var(variable) => {
            if variable >= arity {
                return;
            }

            match &subst[variable] {
                Some(existing) if existing == state => out(subst),
                Some(_) => {}
                None => {
                    subst[variable] = Some(state.clone());
                    out(subst);
                    subst[variable] = None;
                }
            }
        }
        HomLabel::Symbol(symbol) => {
            let term_children = arena.get_children(term);
            inner.step_topdown(state, &mut |rule_symbol, rule_children| {
                if rule_symbol != symbol || rule_children.len() != term_children.len() {
                    return;
                }
                match_topdown_children(
                    arena,
                    term_children,
                    rule_children,
                    arity,
                    inner,
                    subst,
                    0,
                    out,
                );
            });
        }
    }
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn match_topdown_children<A>(
    arena: &TreeArena<HomLabel>,
    term_children: &[HomTerm],
    rule_children: &[A::State],
    arity: usize,
    inner: &A,
    subst: &mut [Option<A::State>],
    position: usize,
    out: &mut dyn FnMut(&mut [Option<A::State>]),
) where
    A: TopDownTa,
{
    if position == term_children.len() {
        out(subst);
        return;
    }

    match_topdown_term(
        arena,
        term_children[position],
        &rule_children[position],
        arity,
        inner,
        subst,
        &mut |subst| {
            match_topdown_children(
                arena,
                term_children,
                rule_children,
                arity,
                inner,
                subst,
                position + 1,
                out,
            );
        },
    );
}

fn emit_if_complete<S: Clone>(
    subst: &[Option<S>],
    children_scratch: &mut SmallVec<[S; 4]>,
    symbols: &SymbolSet,
    out: &mut dyn FnMut(&SymbolSet, &[S]),
) {
    children_scratch.clear();
    for state in subst {
        let Some(state) = state else {
            children_scratch.clear();
            return;
        };
        children_scratch.push(state.clone());
    }
    out(symbols, children_scratch);
}

fn merge_assignments<S: Clone + Eq>(
    left: &[Option<S>],
    right: &[Option<S>],
) -> Option<Vec<Option<S>>> {
    let mut merged = left.to_vec();
    for (idx, value) in right.iter().enumerate() {
        let Some(value) = value else {
            continue;
        };
        match &merged[idx] {
            Some(existing) if existing != value => return None,
            Some(_) => {}
            None => merged[idx] = Some(value.clone()),
        }
    }
    Some(merged)
}

fn eval_condensed_term<A>(
    arena: &TreeArena<HomLabel>,
    term: HomTerm,
    arity: usize,
    expected: Option<&A::State>,
    inner_rules: &[InnerCondensedRule<A::State>],
    inner: &A,
) -> Vec<PartialEval<A::State>>
where
    A: StateUniverse,
{
    match *arena.get_label(term) {
        HomLabel::Var(variable) => {
            if variable >= arity {
                return Vec::new();
            }
            let mut out = Vec::new();
            if let Some(q) = expected {
                let mut assignments = vec![None; arity];
                assignments[variable] = Some(q.clone());
                out.push(PartialEval {
                    assignments,
                    result: q.clone(),
                });
            } else {
                inner.all_states(&mut |q| {
                    let mut assignments = vec![None; arity];
                    assignments[variable] = Some(q.clone());
                    out.push(PartialEval {
                        assignments,
                        result: q,
                    });
                });
            }
            out
        }
        HomLabel::Symbol(symbol) => {
            let term_children = arena.get_children(term);
            let mut out = Vec::new();

            for rule in inner_rules {
                if !rule.symbols.contains(symbol) {
                    continue;
                }
                if rule.children.len() != term_children.len() {
                    continue;
                }
                if let Some(q) = expected
                    && &rule.result != q
                {
                    continue;
                }

                let mut partials = vec![vec![None; arity]];
                for (&child_term, child_state) in term_children.iter().zip(&rule.children) {
                    let child_evals = eval_condensed_term(
                        arena,
                        child_term,
                        arity,
                        Some(child_state),
                        inner_rules,
                        inner,
                    );
                    if child_evals.is_empty() {
                        partials.clear();
                        break;
                    }

                    let mut next = Vec::new();
                    for partial in &partials {
                        for child_eval in &child_evals {
                            if let Some(merged) =
                                merge_assignments(partial, &child_eval.assignments)
                            {
                                next.push(merged);
                            }
                        }
                    }
                    partials = next;
                    if partials.is_empty() {
                        break;
                    }
                }

                for assignments in partials {
                    out.push(PartialEval {
                        assignments,
                        result: rule.result.clone(),
                    });
                }
            }

            out
        }
    }
}

fn collect_inner_condensed_rules<A: CondensedTa>(inner: &A) -> Vec<InnerCondensedRule<A::State>> {
    let mut inner_rules = Vec::new();
    inner.condensed_rules(&mut |children, symbols, result| {
        inner_rules.push(InnerCondensedRule {
            children: children.to_vec(),
            symbols: symbols.clone(),
            result,
        });
    });
    inner_rules
}

impl<A> CondensedTa for InvHom<'_, A>
where
    A: CondensedTa + StateUniverse,
{
    fn condensed_rules(&self, out: &mut dyn FnMut(&[A::State], &SymbolSet, A::State)) {
        let inner_rules = collect_inner_condensed_rules(&self.inner);
        let mut inner_by_symbol: FxHashMap<Symbol, Vec<usize>> = FxHashMap::default();
        for (idx, rule) in inner_rules.iter().enumerate() {
            for symbol in rule.symbols.iter() {
                inner_by_symbol.entry(symbol).or_default().push(idx);
            }
        }

        let mut groups: FxHashMap<(Vec<A::State>, A::State), SymbolSet> = FxHashMap::default();
        for (term_id, labels, term) in self.hom.term_sets() {
            let Some(&first_label) = labels.first() else {
                continue;
            };
            let Some(arity) = self.hom.source_arity(first_label) else {
                continue;
            };

            if let Some(direct) = direct_linear_term(self.hom.arena(), term, arity) {
                if let Some(rule_indexes) = inner_by_symbol.get(&direct.symbol) {
                    for &rule_idx in rule_indexes {
                        let rule = &inner_rules[rule_idx];
                        if rule.children.len() != direct.variables.len() {
                            continue;
                        }

                        let mut children = vec![None; arity];
                        for (&variable, child) in direct.variables.iter().zip(&rule.children) {
                            children[variable] = Some(child.clone());
                        }
                        let Some(children) = children.into_iter().collect::<Option<Vec<_>>>()
                        else {
                            continue;
                        };

                        let sym_set = groups.entry((children, rule.result.clone())).or_default();
                        for &label in self.hom.label_set(term_id) {
                            sym_set.insert(label);
                        }
                    }
                }
                continue;
            }

            let evals = eval_condensed_term(
                self.hom.arena(),
                term,
                arity,
                None,
                &inner_rules,
                &self.inner,
            );
            for eval in evals {
                let Some(children) = eval.assignments.into_iter().collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                let sym_set = groups.entry((children, eval.result)).or_default();
                for &label in self.hom.label_set(term_id) {
                    sym_set.insert(label);
                }
            }
        }

        for ((children, result), symbols) in groups {
            out(&children, &symbols, result);
        }
    }

    fn condensed_nullary_rules(&self, out: &mut dyn FnMut(&SymbolSet, A::State)) {
        let mut fallback = Vec::new();
        for (term_id, labels, term) in self.hom.term_sets() {
            let Some(&first_label) = labels.first() else {
                continue;
            };
            let Some(arity) = self.hom.source_arity(first_label) else {
                continue;
            };
            if arity != 0 {
                continue;
            }

            let mut source_symbols = SymbolSet::new();
            for &label in self.hom.label_set(term_id) {
                source_symbols.insert(label);
            }

            if let Some(direct) = direct_linear_term(self.hom.arena(), term, arity)
                && direct.variables.is_empty()
            {
                self.inner
                    .condensed_nullary_rules(&mut |inner_symbols, result| {
                        if inner_symbols.contains(direct.symbol) {
                            out(&source_symbols, result);
                        }
                    });
                continue;
            }

            fallback.push((source_symbols, term));
        }

        if !fallback.is_empty() {
            let inner_rules = collect_inner_condensed_rules(&self.inner);
            for (symbols, term) in fallback {
                for eval in
                    eval_condensed_term(self.hom.arena(), term, 0, None, &inner_rules, &self.inner)
                {
                    if eval.assignments.is_empty() {
                        out(&symbols, eval.result);
                    }
                }
            }
        }
    }

    fn condensed_rules_by_child(
        &self,
        position: usize,
        state: &A::State,
        out: &mut dyn FnMut(&[A::State], &SymbolSet, A::State),
    ) {
        let mut fallback = Vec::new();
        for (term_id, labels, term) in self.hom.term_sets() {
            let Some(&first_label) = labels.first() else {
                continue;
            };
            let Some(arity) = self.hom.source_arity(first_label) else {
                continue;
            };
            if position >= arity {
                continue;
            }

            let mut source_symbols = SymbolSet::new();
            for &label in self.hom.label_set(term_id) {
                source_symbols.insert(label);
            }

            let Some(direct) = direct_linear_term(self.hom.arena(), term, arity) else {
                fallback.push((source_symbols, term, arity));
                continue;
            };
            let Some(inner_position) = direct
                .variables
                .iter()
                .position(|&variable| variable == position)
            else {
                continue;
            };

            self.inner.condensed_rules_by_child(
                inner_position,
                state,
                &mut |inner_children, inner_symbols, result| {
                    if !inner_symbols.contains(direct.symbol)
                        || inner_children.len() != direct.variables.len()
                    {
                        return;
                    }

                    let mut children = vec![None; arity];
                    for (&variable, child) in direct.variables.iter().zip(inner_children) {
                        children[variable] = Some(child.clone());
                    }
                    let Some(children) = children.into_iter().collect::<Option<Vec<_>>>() else {
                        return;
                    };
                    out(&children, &source_symbols, result);
                },
            );
        }

        if !fallback.is_empty() {
            let inner_rules = collect_inner_condensed_rules(&self.inner);
            for (symbols, term, arity) in fallback {
                for eval in eval_condensed_term(
                    self.hom.arena(),
                    term,
                    arity,
                    None,
                    &inner_rules,
                    &self.inner,
                ) {
                    let Some(children) = eval.assignments.into_iter().collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    if children.get(position) == Some(state) {
                        out(&children, &symbols, eval.result);
                    }
                }
            }
        }
    }
}

impl<A> CondensedTopDownTa for InvHom<'_, A>
where
    A: TopDownTa,
{
    fn condensed_rules_by_parent(
        &self,
        parent: &A::State,
        out: &mut dyn FnMut(&SymbolSet, &[A::State]),
    ) {
        let arena = self.hom.arena();
        let mut source_symbols = SymbolSet::new();
        let mut subst = SmallVec::<[Option<A::State>; 4]>::new();
        let mut children_scratch = SmallVec::<[A::State; 4]>::new();

        for (term_id, labels, term) in self.hom.term_sets() {
            let Some(&first_label) = labels.first() else {
                continue;
            };
            let Some(arity) = self.hom.source_arity(first_label) else {
                continue;
            };

            source_symbols.clear();
            for &label in self.hom.label_set(term_id) {
                source_symbols.insert(label);
            }

            subst.clear();
            subst.resize_with(arity, || None);

            if let Some(direct) = direct_linear_term(arena, term, arity) {
                self.inner
                    .step_topdown(parent, &mut |target_symbol, target_children| {
                        if target_symbol != direct.symbol
                            || target_children.len() != direct.variables.len()
                        {
                            return;
                        }

                        subst.fill(None);
                        for (&variable, child) in direct.variables.iter().zip(target_children) {
                            subst[variable] = Some(child.clone());
                        }
                        emit_if_complete(&subst, &mut children_scratch, &source_symbols, out);
                    });
                continue;
            }

            match_topdown_term(
                arena,
                term,
                parent,
                arity,
                &self.inner,
                &mut subst,
                &mut |subst| {
                    emit_if_complete(subst, &mut children_scratch, &source_symbols, out);
                },
            );
        }
    }

    fn condensed_initial_states(&self, out: &mut dyn FnMut(A::State)) {
        self.inner.initial_states(out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BottomUpTa, DetBottomUpTa, ExplicitBuilder, StateId};
    use std::cell::Cell;

    fn sym(i: u32) -> Symbol {
        Symbol(i)
    }

    fn var(arena: &mut TreeArena<HomLabel>, i: usize) -> HomTerm {
        arena.add_node(HomLabel::Var(i), vec![])
    }

    fn node(arena: &mut TreeArena<HomLabel>, symbol: Symbol, children: Vec<HomTerm>) -> HomTerm {
        arena.add_node(HomLabel::Symbol(symbol), children)
    }

    fn make_inner() -> (crate::Explicit, StateId, StateId, StateId) {
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        let qr = b.new_state();
        b.add_rule(sym(10), vec![q0, q1], qr);
        b.add_accepting(qr);
        (b.build(), q0, q1, qr)
    }

    #[test]
    fn depth1_step_delegates_to_inner() {
        let (inner, q0, q1, qr) = make_inner();
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(10), vec![v0, v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut out = Vec::new();
        inv.step(sym(0), &[q0, q1], &mut |q| out.push(q));
        assert_eq!(out, vec![qr]);
        assert!(inv.is_accepting(&qr));
    }

    #[test]
    fn step_deduplicates_results() {
        #[derive(Clone)]
        struct DuplicateInner;

        impl BottomUpTa for DuplicateInner {
            type State = StateId;

            fn step(&self, _f: Symbol, _children: &[StateId], out: &mut dyn FnMut(StateId)) {
                out(StateId(7));
                out(StateId(7));
            }

            fn is_accepting(&self, _q: &StateId) -> bool {
                false
            }
        }

        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let rhs = node(&mut arena, sym(10), vec![v0]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 1, rhs).unwrap();
        let inv = InvHom::new(DuplicateInner, &hom);

        let mut out = Vec::new();
        inv.step(sym(0), &[StateId(0)], &mut |q| out.push(q));
        assert_eq!(out, vec![StateId(7)]);
    }

    #[test]
    fn depth1_step_det_delegates_to_inner() {
        let (inner, q0, q1, qr) = make_inner();
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(10), vec![v0, v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);
        assert_eq!(inv.step_det(sym(0), &[q0, q1]), Some(qr));
        assert_eq!(inv.step_det(sym(0), &[q1, q0]), None);
    }

    #[test]
    fn unmapped_symbol_emits_nothing() {
        let (inner, q0, q1, _qr) = make_inner();
        let arena = TreeArena::new();
        let hom = Homomorphism::with_arena(arena);
        let inv = InvHom::new(inner, &hom);
        let mut out = Vec::new();
        inv.step(sym(99), &[q0, q1], &mut |q| out.push(q));
        assert!(out.is_empty());
    }

    #[test]
    fn nullary_ground_term_evaluates_correctly() {
        let mut b = ExplicitBuilder::new();
        let qa = b.new_state();
        b.add_rule(sym(20), vec![], qa);
        b.add_accepting(qa);
        let inner = b.build();

        let mut arena = TreeArena::new();
        let rhs = node(&mut arena, sym(20), vec![]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 0, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut out = Vec::new();
        inv.step(sym(0), &[], &mut |q| out.push(q));
        assert_eq!(out, vec![qa]);
        assert!(inv.is_accepting(&qa));
    }

    #[test]
    fn depth2_term_evaluates_correctly() {
        let mut b = ExplicitBuilder::new();
        let q_leaf = b.new_state();
        let q_inner = b.new_state();
        let q1 = b.new_state();
        let qr = b.new_state();
        b.add_rule(sym(5), vec![q_leaf], q_inner);
        b.add_rule(sym(6), vec![q_inner, q1], qr);
        b.add_accepting(qr);
        let inner = b.build();

        let mut arena = TreeArena::new();
        let wrapped_v0 = var(&mut arena, 0);
        let wrapped = node(&mut arena, sym(5), vec![wrapped_v0]);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(6), vec![wrapped, v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut out = Vec::new();
        inv.step(sym(0), &[q_leaf, q1], &mut |q| out.push(q));
        assert_eq!(out, vec![qr]);
    }

    #[test]
    fn condensed_depth1_groups_source_symbols() {
        let (inner, q0, q1, qr) = make_inner();
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(10), vec![v0, v1]);
        let same_v0 = var(&mut arena, 0);
        let same_v1 = var(&mut arena, 1);
        let same = node(&mut arena, sym(10), vec![same_v0, same_v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        hom.add(sym(1), 2, same).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut groups = Vec::new();
        inv.condensed_rules(&mut |children, symbols, result| {
            groups.push((children.to_vec(), symbols.clone(), result));
        });

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].0, vec![q0, q1]);
        assert!(groups[0].1.contains(sym(0)));
        assert!(groups[0].1.contains(sym(1)));
        assert_eq!(groups[0].2, qr);
    }

    #[test]
    fn indexed_condensed_depth1_uses_hom_label_sets() {
        let (inner, q0, q1, qr) = make_inner();
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(10), vec![v0, v1]);
        let same_v0 = var(&mut arena, 0);
        let same_v1 = var(&mut arena, 1);
        let same = node(&mut arena, sym(10), vec![same_v0, same_v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        hom.add(sym(1), 2, same).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut groups = Vec::new();
        inv.condensed_rules_by_child(0, &q0, &mut |children, symbols, result| {
            groups.push((children.to_vec(), symbols.clone(), result));
        });

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].0, vec![q0, q1]);
        assert!(groups[0].1.contains(sym(0)));
        assert!(groups[0].1.contains(sym(1)));
        assert_eq!(groups[0].2, qr);
    }

    #[test]
    fn topdown_condensed_depth1_uses_hom_label_sets() {
        let (inner, q0, q1, qr) = make_inner();
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(10), vec![v0, v1]);
        let same_v0 = var(&mut arena, 0);
        let same_v1 = var(&mut arena, 1);
        let same = node(&mut arena, sym(10), vec![same_v0, same_v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        hom.add(sym(1), 2, same).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut groups = Vec::new();
        inv.condensed_rules_by_parent(&qr, &mut |symbols, children| {
            groups.push((children.to_vec(), symbols.clone()));
        });

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].0, vec![q0, q1]);
        assert!(groups[0].1.contains(sym(0)));
        assert!(groups[0].1.contains(sym(1)));
    }

    #[test]
    fn condensed_nested_rhs_matches_step_enumeration() {
        let mut b = ExplicitBuilder::new();
        let q_leaf = b.new_state();
        let q_inner = b.new_state();
        let q1 = b.new_state();
        let qr = b.new_state();
        b.add_rule(sym(5), vec![q_leaf], q_inner);
        b.add_rule(sym(6), vec![q_inner, q1], qr);
        let inner = b.build();

        let mut arena = TreeArena::new();
        let wrapped_v0 = var(&mut arena, 0);
        let wrapped = node(&mut arena, sym(5), vec![wrapped_v0]);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(6), vec![wrapped, v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut condensed = Vec::new();
        inv.condensed_rules(&mut |children, symbols, result| {
            for src in symbols.iter() {
                condensed.push((src, children.to_vec(), result));
            }
        });

        let mut stepped = Vec::new();
        inv.step(sym(0), &[q_leaf, q1], &mut |q| {
            stepped.push((sym(0), vec![q_leaf, q1], q));
        });
        condensed.sort();
        stepped.sort();
        assert_eq!(condensed, stepped);
    }

    #[test]
    fn topdown_condensed_nested_rhs_streams_matches() {
        let mut b = ExplicitBuilder::new();
        let q_leaf = b.new_state();
        let q_inner = b.new_state();
        let q1 = b.new_state();
        let qr = b.new_state();
        b.add_rule(sym(5), vec![q_leaf], q_inner);
        b.add_rule(sym(6), vec![q_inner, q1], qr);
        let inner = b.build();

        let mut arena = TreeArena::new();
        let wrapped_v0 = var(&mut arena, 0);
        let wrapped = node(&mut arena, sym(5), vec![wrapped_v0]);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(6), vec![wrapped, v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut groups = Vec::new();
        inv.condensed_rules_by_parent(&qr, &mut |symbols, children| {
            groups.push((children.to_vec(), symbols.clone()));
        });

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].0, vec![q_leaf, q1]);
        assert!(groups[0].1.contains(sym(0)));
    }

    #[test]
    fn condensed_supports_ground_subterms() {
        let mut b = ExplicitBuilder::new();
        let qa = b.new_state();
        let qx = b.new_state();
        let qr = b.new_state();
        b.add_rule(sym(3), vec![], qa);
        b.add_rule(sym(4), vec![qa, qx], qr);
        let inner = b.build();

        let mut arena = TreeArena::new();
        let ground = node(&mut arena, sym(3), vec![]);
        let v0 = var(&mut arena, 0);
        let rhs = node(&mut arena, sym(4), vec![ground, v0]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 1, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut groups = Vec::new();
        inv.condensed_rules(&mut |children, symbols, result| {
            groups.push((children.to_vec(), symbols.clone(), result));
        });

        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].0, vec![qx]);
        assert!(groups[0].1.contains(sym(0)));
        assert_eq!(groups[0].2, qr);
    }

    #[test]
    fn condensed_supports_bare_variable_rhs() {
        let mut b = ExplicitBuilder::new();
        let q0 = b.new_state();
        let q1 = b.new_state();
        b.add_rule(sym(10), vec![], q0);
        b.add_rule(sym(11), vec![], q1);
        let inner = b.build();

        let mut arena = TreeArena::new();
        let rhs = var(&mut arena, 0);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 1, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut groups = Vec::new();
        inv.condensed_rules(&mut |children, symbols, result| {
            groups.push((children.to_vec(), symbols.clone(), result));
        });
        groups.sort_by_key(|(children, _, result)| (children.clone(), *result));

        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0].0, vec![q0]);
        assert_eq!(groups[0].2, q0);
        assert!(groups[0].1.contains(sym(0)));
        assert_eq!(groups[1].0, vec![q1]);
        assert_eq!(groups[1].2, q1);
        assert!(groups[1].1.contains(sym(0)));
    }

    #[test]
    fn condensed_constrained_variables_do_not_enumerate_universe() {
        struct CountingInner {
            all_states_calls: Cell<usize>,
        }

        impl BottomUpTa for CountingInner {
            type State = u8;

            fn step(&self, _f: Symbol, _children: &[u8], _out: &mut dyn FnMut(u8)) {}

            fn is_accepting(&self, q: &u8) -> bool {
                *q == 2
            }
        }

        impl StateUniverse for CountingInner {
            fn all_states(&self, _out: &mut dyn FnMut(u8)) {
                self.all_states_calls.set(self.all_states_calls.get() + 1);
            }
        }

        impl CondensedTa for CountingInner {
            fn condensed_rules(&self, out: &mut dyn FnMut(&[u8], &SymbolSet, u8)) {
                let mut symbols = SymbolSet::new();
                symbols.insert(sym(10));
                out(&[0, 1], &symbols, 2);
            }
        }

        let inner = CountingInner {
            all_states_calls: Cell::new(0),
        };
        let mut arena = TreeArena::new();
        let v0 = var(&mut arena, 0);
        let v1 = var(&mut arena, 1);
        let rhs = node(&mut arena, sym(10), vec![v0, v1]);
        let mut hom = Homomorphism::with_arena(arena);
        hom.add(sym(0), 2, rhs).unwrap();
        let inv = InvHom::new(inner, &hom);

        let mut rules = Vec::new();
        inv.condensed_rules(&mut |children, symbols, result| {
            rules.push((children.to_vec(), symbols.clone(), result));
        });

        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].0, vec![0, 1]);
        assert_eq!(rules[0].2, 2);
        assert_eq!(inv.inner().all_states_calls.get(), 0);
    }
}
