//! Homomorphism-RHS-condensed sibling-finder execution.

use super::*;
use crate::{KeySet, SetTrie};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RhsItem {
    right: StateId,
    children: SmallVec<[StateId; 4]>,
}

struct RhsNodeChart<K> {
    items: Vec<RhsItem>,
    seen_by_hash: FxHashMap<u64, SmallVec<[usize; 1]>>,
    binary_index: BinaryIndex<K>,
}

impl<K> Default for RhsNodeChart<K> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            seen_by_hash: FxHashMap::default(),
            binary_index: BinaryIndex::default(),
        }
    }
}

/// A chart shared by every source rule whose label has the same homomorphic
/// image. Items retain only the decomposition children of the condensed rule;
/// grammar-rule and product-state information stays in the intersection index.
struct RhsChart<K> {
    nodes: Vec<RhsNodeChart<K>>,
    agenda: Vec<(usize, usize)>,
    root_by_child: Vec<FxHashMap<StateId, Vec<usize>>>,
    // Product IDs below this cutoff already existed when the root was first
    // matched. Later partner-triggered matches need only consider newer IDs.
    root_birth: Vec<usize>,
    activated: Vec<crate::FxHashSet<StateId>>,
    initialized: bool,
}

impl<K> RhsChart<K> {
    fn new(node_count: usize, arity: usize) -> Self {
        Self {
            nodes: (0..node_count).map(|_| RhsNodeChart::default()).collect(),
            agenda: Vec::new(),
            root_by_child: (0..arity).map(|_| FxHashMap::default()).collect(),
            root_birth: Vec::new(),
            activated: (0..arity).map(|_| crate::FxHashSet::default()).collect(),
            initialized: false,
        }
    }
}

impl<K: Clone + Eq + Hash> RhsChart<K> {
    fn insert(&mut self, node: usize, item: RhsItem, stats: &mut SiblingIntersectionStats) {
        let chart = &mut self.nodes[node];
        let mut hasher = rustc_hash::FxHasher::default();
        item.hash(&mut hasher);
        let hash = hasher.finish();
        if chart
            .seen_by_hash
            .get(&hash)
            .is_some_and(|ids| ids.iter().any(|&id| chart.items[id] == item))
        {
            return;
        }
        let item_id = chart.items.len();
        chart.items.push(item);
        chart.seen_by_hash.entry(hash).or_default().push(item_id);
        self.agenda.push((node, item_id));
        stats.term_items += 1;
    }

    #[allow(clippy::too_many_arguments)]
    fn initialize<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        decomp: &D,
        right_states: &mut Interner<D::State>,
        new_roots: &mut Vec<usize>,
        stats: &mut SiblingIntersectionStats,
        control: &ParseControl,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
    {
        if !self.initialized {
            self.initialized = true;
            for (node, node_plan) in plan.nodes.iter().enumerate() {
                let CompiledNode::Operation { symbol, children } = &node_plan.kind else {
                    continue;
                };
                if !children.is_empty() {
                    continue;
                }
                stats.right_step_calls += 1;
                let mut results = SmallVec::<[StateId; 2]>::new();
                decomp.step(*symbol, &[], &mut |result| {
                    results.push(right_states.intern(result));
                });
                for right in results {
                    self.insert(
                        node,
                        RhsItem {
                            right,
                            children: smallvec::smallvec![StateId::STUCK; plan.arity],
                        },
                        stats,
                    );
                }
            }
        }
        self.propagate(plan, decomp, right_states, new_roots, stats, control)
    }

    #[allow(clippy::too_many_arguments)]
    fn activate<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        variable: usize,
        right: StateId,
        decomp: &D,
        right_states: &mut Interner<D::State>,
        new_roots: &mut Vec<usize>,
        stats: &mut SiblingIntersectionStats,
        control: &ParseControl,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
    {
        if self.activated[variable].contains(&right) {
            return Ok(());
        }
        self.initialize(plan, decomp, right_states, new_roots, stats, control)?;
        self.activated[variable].insert(right);
        let mut children = smallvec::smallvec![StateId::STUCK; plan.arity];
        children[variable] = right;
        self.insert(
            plan.variable_nodes[variable],
            RhsItem { right, children },
            stats,
        );
        self.propagate(plan, decomp, right_states, new_roots, stats, control)
    }

    #[allow(clippy::too_many_arguments)]
    fn propagate<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        decomp: &D,
        right_states: &mut Interner<D::State>,
        new_roots: &mut Vec<usize>,
        stats: &mut SiblingIntersectionStats,
        control: &ParseControl,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
    {
        while let Some((node, item_id)) = self.agenda.pop() {
            control.check()?;
            if node == plan.root {
                let item = &self.nodes[node].items[item_id];
                if self.root_birth.len() <= item_id {
                    self.root_birth.resize(item_id + 1, usize::MAX);
                }
                for (position, &child) in item.children.iter().enumerate() {
                    self.root_by_child[position]
                        .entry(child)
                        .or_default()
                        .push(item_id);
                }
                new_roots.push(item_id);
                stats.root_items += 1;
                continue;
            }

            let link = plan.nodes[node]
                .parent
                .expect("every non-root compiled node has a parent");
            let CompiledNode::Operation { symbol, children } = &plan.nodes[link.node].kind else {
                unreachable!("variables cannot have children");
            };
            match children.len() {
                1 => {
                    let item = self.nodes[node].items[item_id].clone();
                    let raw = right_states.resolve(item.right).clone();
                    stats.right_step_calls += 1;
                    let mut results = SmallVec::<[StateId; 2]>::new();
                    decomp.step(*symbol, &[raw], &mut |result| {
                        results.push(right_states.intern(result));
                    });
                    for right in results {
                        self.insert(
                            link.node,
                            RhsItem {
                                right,
                                children: item.children.clone(),
                            },
                            stats,
                        );
                    }
                }
                2 => {
                    let item = self.nodes[node].items[item_id].clone();
                    let raw = right_states.resolve(item.right).clone();
                    let Some(key) = decomp.sibling_key(*symbol, link.position, &raw) else {
                        continue;
                    };
                    let other_position = 1 - link.position;
                    let partner_count = self.nodes[link.node].binary_index.positions
                        [other_position]
                        .get(&key)
                        .map_or(0, Vec::len);
                    let partner_key = key.clone();
                    self.nodes[link.node].binary_index.positions[link.position]
                        .entry(key)
                        .or_default()
                        .push(item_id);

                    let other_node = children[other_position];
                    for partner_index in 0..partner_count {
                        let partner_id = self.nodes[link.node].binary_index.positions
                            [other_position][&partner_key][partner_index];
                        stats.partner_candidates += 1;
                        let partner = &self.nodes[other_node].items[partner_id];
                        let (left, right) = if link.position == 0 {
                            (&item, partner)
                        } else {
                            (partner, &item)
                        };
                        let Some(assignments) = merge_assignments(&left.children, &right.children)
                        else {
                            continue;
                        };
                        let raw_children = [
                            right_states.resolve(left.right).clone(),
                            right_states.resolve(right.right).clone(),
                        ];
                        stats.right_step_calls += 1;
                        let mut results = SmallVec::<[StateId; 2]>::new();
                        decomp.step(*symbol, &raw_children, &mut |result| {
                            results.push(right_states.intern(result));
                        });
                        for right in results {
                            self.insert(
                                link.node,
                                RhsItem {
                                    right,
                                    children: assignments.clone(),
                                },
                                stats,
                            );
                        }
                    }
                }
                _ => unreachable!("rank above two was rejected while compiling"),
            }
        }
        Ok(())
    }

    fn root(&self, plan: &CompiledTerm, root: usize) -> &RhsItem {
        &self.nodes[plan.root].items[root]
    }

    fn roots_with_child(&self, position: usize, right: StateId) -> &[usize] {
        self.root_by_child[position]
            .get(&right)
            .map_or(&[], Vec::as_slice)
    }

    fn mark_root_born(&mut self, root: usize, product_count: usize) {
        debug_assert_eq!(self.root_birth[root], usize::MAX);
        self.root_birth[root] = product_count;
    }

    fn root_birth(&self, root: usize) -> usize {
        let birth = self.root_birth[root];
        debug_assert_ne!(birth, usize::MAX);
        birth
    }
}

fn merge_assignments(left: &[StateId], right: &[StateId]) -> Option<SmallVec<[StateId; 4]>> {
    let mut merged = SmallVec::from_slice(left);
    for (slot, &state) in right.iter().enumerate() {
        if state == StateId::STUCK {
            continue;
        }
        if merged[slot] != StateId::STUCK && merged[slot] != state {
            return None;
        }
        merged[slot] = state;
    }
    Some(merged)
}

struct ProductLeftSet<'a>(&'a FxHashMap<StateId, StateId>);

impl KeySet<StateId> for ProductLeftSet<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn contains(&self, key: &StateId) -> bool {
        self.0.contains_key(key)
    }

    fn for_each(&self, out: &mut dyn FnMut(&StateId)) {
        for state in self.0.keys() {
            out(state);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn try_emit<D: BottomUpTa>(
    rule_id: usize,
    root: &RhsItem,
    rules: &[LeftRule],
    left: &Explicit,
    decomp: &D,
    right_states: &Interner<D::State>,
    products: &mut ProductMap,
    pairs: &mut Vec<(StateId, StateId)>,
    trigger: Option<(usize, StateId, usize)>,
    builder: &mut ExplicitBuilder,
    agenda: &mut VecDeque<(StateId, StateId, StateId)>,
) {
    let rule = &rules[rule_id];
    if trigger.is_some_and(|(_, product, root_birth)| product.index() < root_birth) {
        return;
    }
    let mut product_children = SmallVec::<[StateId; 2]>::new();
    for (&left_child, &right_child) in rule.children.iter().zip(&root.children) {
        let Some(product) = products.get(left_child, right_child) else {
            return;
        };
        product_children.push(product);
    }
    if let Some((trigger_position, trigger_product, _)) = trigger {
        // Product IDs follow agenda creation order. The first occurrence of
        // the greatest child ID is therefore a unique trigger for this rule.
        let mut latest_position = 0;
        for position in 1..product_children.len() {
            if product_children[position].0 > product_children[latest_position].0 {
                latest_position = position;
            }
        }
        if latest_position != trigger_position
            || product_children[latest_position] != trigger_product
        {
            return;
        }
    }
    let (parent, is_new) = product_id(
        rule.result,
        root.right,
        left,
        decomp,
        right_states,
        products,
        pairs,
        builder,
    );
    if is_new {
        agenda.push_back((rule.result, root.right, parent));
    }
    builder.add_weighted_rule_inline(rule.symbol, product_children, parent, rule.weight);
}

#[allow(clippy::type_complexity)]
pub(super) fn materialize<D>(
    left: &Explicit,
    decomp: &D,
    hom: &Homomorphism,
    control: &ParseControl,
) -> Result<
    (
        Explicit,
        Interner<D::State>,
        Vec<(StateId, StateId)>,
        SiblingIntersectionStats,
    ),
    SiblingIntersectionError,
>
where
    D: SiblingKeyedTa,
    D::State: Clone + Eq + Hash,
{
    control.check()?;
    let mut programs = Vec::<CompiledTerm>::new();
    let mut program_by_term = FxHashMap::<usize, usize>::default();
    let mut rules = Vec::<LeftRule>::new();

    for rule in left.rules() {
        let Some(term_id) = hom.term_id(rule.symbol) else {
            continue;
        };
        let program = if let Some(&program) = program_by_term.get(&term_id) {
            program
        } else {
            let program = programs.len();
            programs.push(compile_term(
                hom.arena(),
                hom.term_by_id(term_id),
                rule.children.len(),
            )?);
            program_by_term.insert(term_id, program);
            program
        };
        debug_assert_eq!(programs[program].arity, rule.children.len());
        rules.push(LeftRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
            weight: rule.weight,
            program,
        });
    }

    let mut program_left_indexes: Vec<SetTrie<StateId, Vec<usize>>> =
        (0..programs.len()).map(|_| SetTrie::new()).collect();
    let mut by_left_child = vec![Vec::<(usize, usize)>::new(); left.num_states() as usize];
    let mut nullary_programs = Vec::new();
    let mut nullary_seen = vec![false; programs.len()];
    for (rule_id, rule) in rules.iter().enumerate() {
        program_left_indexes[rule.program]
            .get_or_insert_with(&rule.children, Vec::new)
            .push(rule_id);
        if rule.children.is_empty() && !nullary_seen[rule.program] {
            nullary_seen[rule.program] = true;
            nullary_programs.push(rule.program);
        }
        for (position, &child) in rule.children.iter().enumerate() {
            by_left_child[child.index()].push((rule_id, position));
        }
    }

    let mut charts: Vec<RhsChart<D::Key>> = programs
        .iter()
        .map(|program| RhsChart::new(program.nodes.len(), program.arity))
        .collect();
    let mut right_states = Interner::new();
    let mut products = ProductMap::default();
    let mut pairs = Vec::new();
    let mut builder = ExplicitBuilder::new();
    let mut agenda = VecDeque::<(StateId, StateId, StateId)>::new();
    let mut stats = SiblingIntersectionStats::default();
    let mut new_roots = Vec::<usize>::new();
    let mut candidate_rules = Vec::<usize>::new();
    let mut activation_offsets = Vec::with_capacity(programs.len() + 1);
    activation_offsets.push(0);
    for program in &programs {
        activation_offsets.push(activation_offsets.last().copied().unwrap() + program.arity);
    }
    let mut activation_seen = vec![false; *activation_offsets.last().unwrap()];
    let mut existing_counts = vec![0; activation_seen.len()];
    let mut activation_slots = Vec::<(usize, usize, usize)>::new();

    for program in nullary_programs {
        new_roots.clear();
        charts[program].initialize(
            &programs[program],
            decomp,
            &mut right_states,
            &mut new_roots,
            &mut stats,
            control,
        )?;
        for root_id in new_roots.drain(..) {
            charts[program].mark_root_born(root_id, pairs.len());
            let root = charts[program].root(&programs[program], root_id);
            program_left_indexes[program].for_each_value_for_key_sets(
                &[] as &[ProductLeftSet<'_>],
                |candidate_rules| {
                    for &rule_id in candidate_rules {
                        try_emit(
                            rule_id,
                            root,
                            &rules,
                            left,
                            decomp,
                            &right_states,
                            &mut products,
                            &mut pairs,
                            None,
                            &mut builder,
                            &mut agenda,
                        );
                    }
                },
            );
        }
    }

    while let Some((left_state, right_state, product)) = agenda.pop_front() {
        control.check()?;
        stats.agenda_pops += 1;
        let occurrences = &by_left_child[left_state.index()];
        activation_slots.clear();
        for &(rule_id, position) in occurrences {
            let program = rules[rule_id].program;
            let slot = activation_offsets[program] + position;
            if !activation_seen[slot] {
                activation_seen[slot] = true;
                existing_counts[slot] = charts[program]
                    .roots_with_child(position, right_state)
                    .len();
                activation_slots.push((program, position, slot));
            }
        }

        for &(program, position, _) in &activation_slots {
            new_roots.clear();
            charts[program].activate(
                &programs[program],
                position,
                right_state,
                decomp,
                &mut right_states,
                &mut new_roots,
                &mut stats,
                control,
            )?;

            for root_id in new_roots.drain(..) {
                charts[program].mark_root_born(root_id, pairs.len());
                let root = charts[program].root(&programs[program], root_id);
                let mut child_sets = SmallVec::<[ProductLeftSet<'_>; 4]>::new();
                let mut complete = true;
                for child in &root.children {
                    if let Some(row) = products.by_right.get(child.index()) {
                        child_sets.push(ProductLeftSet(row));
                    } else {
                        complete = false;
                        break;
                    }
                }
                if !complete {
                    continue;
                }
                candidate_rules.clear();
                program_left_indexes[program].for_each_value_for_key_sets(&child_sets, |matches| {
                    candidate_rules.extend_from_slice(matches);
                });
                drop(child_sets);
                for &candidate in &candidate_rules {
                    try_emit(
                        candidate,
                        root,
                        &rules,
                        left,
                        decomp,
                        &right_states,
                        &mut products,
                        &mut pairs,
                        None,
                        &mut builder,
                        &mut agenda,
                    );
                }
            }
        }

        for &(rule_id, position) in occurrences {
            let program = rules[rule_id].program;
            let slot = activation_offsets[program] + position;
            let root_count = existing_counts[slot];
            for index in 0..root_count {
                let root_id = charts[program].roots_with_child(position, right_state)[index];
                let root = charts[program].root(&programs[program], root_id);
                let root_birth = charts[program].root_birth(root_id);
                try_emit(
                    rule_id,
                    root,
                    &rules,
                    left,
                    decomp,
                    &right_states,
                    &mut products,
                    &mut pairs,
                    Some((position, product, root_birth)),
                    &mut builder,
                    &mut agenda,
                );
            }
        }
        for &(_, _, slot) in &activation_slots {
            activation_seen[slot] = false;
        }
    }

    stats.output_states = pairs.len();
    let chart = builder.build_trusted();
    stats.output_rules = chart.rules().count();
    Ok((chart, right_states, pairs, stats))
}
