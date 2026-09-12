//! Homomorphism-RHS-condensed sibling-finder execution.

use super::*;
use crate::{
    ExplicitBuilder, KeySet, SetTrie,
    materialize::{
        OwnedRule, ProductStateMap, TrustedRuleTracker, current_product_is_latest,
        get_or_create_product_id,
    },
};
use std::{collections::VecDeque, hash::Hasher};

struct RhsNodeChart<K> {
    items: Vec<StateId>,
    // Row-major child assignments; every item occupies this node's stride.
    assignments: Vec<StateId>,
    assignment_width: usize,
    seen_by_hash: FxHashMap<u64, SmallVec<[usize; 1]>>,
    binary_index: Option<BinaryIndex<K>>,
}

impl<K> RhsNodeChart<K> {
    fn new(assignment_width: usize, is_binary: bool) -> Self {
        Self {
            items: Vec::new(),
            assignments: Vec::new(),
            assignment_width,
            seen_by_hash: FxHashMap::default(),
            binary_index: is_binary.then(BinaryIndex::default),
        }
    }
}

/// A chart shared by every source rule whose label has the same homomorphic
/// image. Items retain only the decomposition children of the condensed rule;
/// grammar-rule and product-state information stays in the intersection index.
struct RhsChart<K> {
    nodes: Vec<RhsNodeChart<K>>,
    agenda: Vec<(usize, usize)>,
    assignment_scratch: Vec<StateId>,
    root_by_child: Vec<FxHashMap<StateId, Vec<usize>>>,
    // Product IDs below this cutoff already existed when the root was first
    // matched. Later partner-triggered matches need only consider newer IDs.
    root_birth: Vec<usize>,
    activated: Vec<crate::FxHashSet<StateId>>,
    initialized: bool,
}

struct RhsEvaluation<'a, D: BottomUpTa> {
    decomp: &'a D,
    right_states: &'a mut Interner<D::State>,
    stats: &'a mut SiblingIntersectionStats,
    control: &'a ParseControl,
}

impl<K> RhsChart<K> {
    fn new(plan: &CompiledTerm) -> Self {
        Self {
            nodes: plan
                .nodes
                .iter()
                .map(|node| {
                    RhsNodeChart::new(
                        node.assignment_width,
                        node.operation
                            .as_ref()
                            .is_some_and(|operation| operation.children.len() == 2),
                    )
                })
                .collect(),
            agenda: Vec::new(),
            assignment_scratch: Vec::with_capacity(plan.arity()),
            root_by_child: (0..plan.arity()).map(|_| FxHashMap::default()).collect(),
            root_birth: Vec::new(),
            activated: (0..plan.arity())
                .map(|_| crate::FxHashSet::default())
                .collect(),
            initialized: false,
        }
    }
}

impl<K: Clone + Eq + Hash> RhsChart<K> {
    fn insert(
        &mut self,
        node: usize,
        right: StateId,
        assignment: &[StateId],
        stats: &mut SiblingIntersectionStats,
    ) {
        let chart = &mut self.nodes[node];
        let width = chart.assignment_width;
        debug_assert_eq!(assignment.len(), width);
        let mut hasher = rustc_hash::FxHasher::default();
        right.hash(&mut hasher);
        assignment.hash(&mut hasher);
        let hash = hasher.finish();
        if chart.seen_by_hash.get(&hash).is_some_and(|ids| {
            ids.iter().any(|&id| {
                let start = id * width;
                chart.items[id] == right
                    && chart.assignments[start..start + width] == assignment[..]
            })
        }) {
            return;
        }
        let item_id = chart.items.len();
        chart.items.push(right);
        chart.assignments.extend_from_slice(assignment);
        chart.seen_by_hash.entry(hash).or_default().push(item_id);
        self.agenda.push((node, item_id));
        stats.term_items += 1;
    }

    fn assignment(&self, node: usize, item: usize) -> &[StateId] {
        let chart = &self.nodes[node];
        let start = item * chart.assignment_width;
        &chart.assignments[start..start + chart.assignment_width]
    }

    fn initialize<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        evaluation: &mut RhsEvaluation<'_, D>,
        new_roots: &mut Vec<usize>,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
    {
        if !self.initialized {
            self.initialized = true;
            let mut assignment = std::mem::take(&mut self.assignment_scratch);
            assignment.clear();
            for (node, node_plan) in plan.nodes.iter().enumerate() {
                let Some(CompiledOperation { symbol, children }) = &node_plan.operation else {
                    continue;
                };
                if !children.is_empty() {
                    continue;
                }
                evaluation.stats.right_step_calls += 1;
                let mut results = SmallVec::<[StateId; 2]>::new();
                evaluation.decomp.step(*symbol, &[], &mut |result| {
                    results.push(evaluation.right_states.intern(result));
                });
                for right in results {
                    self.insert(node, right, &assignment, evaluation.stats);
                }
            }
            assignment.clear();
            self.assignment_scratch = assignment;
        }
        self.propagate(plan, evaluation, new_roots)
    }

    fn activate<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        variable: usize,
        right: StateId,
        evaluation: &mut RhsEvaluation<'_, D>,
        new_roots: &mut Vec<usize>,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
    {
        if !self.activated[variable].insert(right) {
            return Ok(());
        }
        self.initialize(plan, evaluation, new_roots)?;
        let mut assignment = std::mem::take(&mut self.assignment_scratch);
        assignment.clear();
        assignment.push(right);
        self.insert(
            plan.variable_nodes[variable],
            right,
            &assignment,
            evaluation.stats,
        );
        assignment.clear();
        self.assignment_scratch = assignment;
        self.propagate(plan, evaluation, new_roots)
    }

    fn propagate<D: SiblingKeyedTa<Key = K>>(
        &mut self,
        plan: &CompiledTerm,
        evaluation: &mut RhsEvaluation<'_, D>,
        new_roots: &mut Vec<usize>,
    ) -> Result<(), SiblingIntersectionError>
    where
        D::State: Clone,
    {
        let mut assignment = std::mem::take(&mut self.assignment_scratch);
        while let Some((node, item_id)) = self.agenda.pop() {
            evaluation.control.check()?;
            if node == ROOT_NODE {
                if self.root_birth.len() <= item_id {
                    self.root_birth.resize(item_id + 1, usize::MAX);
                }
                for position in 0..plan.arity() {
                    let child = self.assignment(node, item_id)[position];
                    self.root_by_child[position]
                        .entry(child)
                        .or_default()
                        .push(item_id);
                }
                new_roots.push(item_id);
                evaluation.stats.root_items += 1;
                continue;
            }

            let link = plan.nodes[node]
                .parent
                .expect("every non-root compiled node has a parent");
            let Some(CompiledOperation { symbol, children }) = &plan.nodes[link.node].operation
            else {
                unreachable!("a variable cannot be a parent node");
            };
            match children.len() {
                1 => {
                    let item = self.nodes[node].items[item_id];
                    let raw = evaluation.right_states.resolve(item).clone();
                    evaluation.stats.right_step_calls += 1;
                    let mut results = SmallVec::<[StateId; 2]>::new();
                    evaluation.decomp.step(*symbol, &[raw], &mut |result| {
                        results.push(evaluation.right_states.intern(result));
                    });
                    copy_assignment_into(
                        self.assignment(node, item_id),
                        if link.node == ROOT_NODE {
                            plan.root_permutation.as_slice()
                        } else {
                            &[]
                        },
                        &mut assignment,
                    );
                    for right in results {
                        self.insert(link.node, right, &assignment, evaluation.stats);
                    }
                }
                2 => {
                    let item = self.nodes[node].items[item_id];
                    let raw = evaluation.right_states.resolve(item).clone();
                    let Some(key) = evaluation.decomp.sibling_key(*symbol, link.position, &raw)
                    else {
                        continue;
                    };
                    let other_position = 1 - link.position;
                    let partner_key = key.clone();
                    let partner_count = {
                        let binary_index = self.nodes[link.node]
                            .binary_index
                            .as_mut()
                            .expect("binary operation nodes have a sibling index");
                        let partner_count = binary_index.positions[other_position]
                            .get(&key)
                            .map_or(0, Vec::len);
                        binary_index.positions[link.position]
                            .entry(key)
                            .or_default()
                            .push(item_id);
                        partner_count
                    };

                    let other_node = children[other_position];
                    for partner_index in 0..partner_count {
                        let partner_id = self.nodes[link.node]
                            .binary_index
                            .as_ref()
                            .expect("binary operation nodes have a sibling index")
                            .positions[other_position][&partner_key][partner_index];
                        evaluation.stats.partner_candidates += 1;
                        let partner = &self.nodes[other_node].items[partner_id];
                        let (left, right) = if link.position == 0 {
                            (item, *partner)
                        } else {
                            (*partner, item)
                        };
                        let (left_node, left_id, right_node, right_id) = if link.position == 0 {
                            (node, item_id, other_node, partner_id)
                        } else {
                            (other_node, partner_id, node, item_id)
                        };
                        merge_assignments_into(
                            self.assignment(left_node, left_id),
                            self.assignment(right_node, right_id),
                            if link.node == ROOT_NODE {
                                plan.root_permutation.as_slice()
                            } else {
                                &[]
                            },
                            &mut assignment,
                        );
                        let raw_children = [
                            evaluation.right_states.resolve(left).clone(),
                            evaluation.right_states.resolve(right).clone(),
                        ];
                        evaluation.stats.right_step_calls += 1;
                        let mut results = SmallVec::<[StateId; 2]>::new();
                        evaluation
                            .decomp
                            .step(*symbol, &raw_children, &mut |result| {
                                results.push(evaluation.right_states.intern(result));
                            });
                        for right in results {
                            self.insert(link.node, right, &assignment, evaluation.stats);
                        }
                    }
                }
                _ => unreachable!("rank above two was rejected while compiling"),
            }
        }
        assignment.clear();
        self.assignment_scratch = assignment;
        Ok(())
    }

    fn root(&self, root: usize) -> (StateId, &[StateId]) {
        (
            self.nodes[ROOT_NODE].items[root],
            self.assignment(ROOT_NODE, root),
        )
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

fn merge_assignments_into(
    left: &[StateId],
    right: &[StateId],
    permutation: &[usize],
    merged: &mut Vec<StateId>,
) {
    merged.clear();
    if permutation.is_empty() {
        merged.extend_from_slice(left);
        merged.extend_from_slice(right);
        return;
    }
    merged.reserve(permutation.len());
    for &offset in permutation {
        if offset < left.len() {
            merged.push(left[offset]);
        } else {
            merged.push(right[offset - left.len()]);
        }
    }
}

fn copy_assignment_into(source: &[StateId], permutation: &[usize], target: &mut Vec<StateId>) {
    target.clear();
    if permutation.is_empty() {
        target.extend_from_slice(source);
        return;
    }
    target.reserve(permutation.len());
    target.extend(permutation.iter().map(|&offset| source[offset]));
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

struct OccurrenceGroup {
    program: usize,
    position: usize,
    rule_ids: Vec<usize>,
}

struct SiblingIntersection<'a, D: BottomUpTa> {
    left: &'a Explicit,
    decomp: &'a D,
    right_states: Interner<D::State>,
    products: ProductStateMap,
    pairs: Vec<(StateId, StateId)>,
    builder: ExplicitBuilder,
    rule_tracker: TrustedRuleTracker,
    agenda: VecDeque<(StateId, StateId, StateId)>,
    stats: SiblingIntersectionStats,
}

impl<'a, D: BottomUpTa> SiblingIntersection<'a, D> {
    fn new(left: &'a Explicit, decomp: &'a D) -> Self {
        Self {
            left,
            decomp,
            right_states: Interner::new(),
            products: ProductStateMap::new(),
            pairs: Vec::new(),
            builder: ExplicitBuilder::new(),
            rule_tracker: TrustedRuleTracker::default(),
            agenda: VecDeque::new(),
            stats: SiblingIntersectionStats::default(),
        }
    }

    fn emit(
        &mut self,
        rule: &OwnedRule,
        root_right: StateId,
        root_children: &[StateId],
        trigger: Option<(usize, StateId, usize)>,
    ) {
        if trigger.is_some_and(|(_, product, root_birth)| product.index() < root_birth) {
            return;
        }
        let mut product_children = SmallVec::<[StateId; 2]>::new();
        for (&left_child, &right_child) in rule.children.iter().zip(root_children) {
            let Some(product) = self.products.get(left_child, right_child) else {
                return;
            };
            product_children.push(product);
        }
        if let Some((trigger_position, trigger_product, _)) = trigger
            && !current_product_is_latest(&product_children, trigger_position, trigger_product)
        {
            return;
        }
        let (parent, is_new) = get_or_create_product_id(
            rule.result,
            root_right,
            self.left,
            self.decomp,
            &mut self.products,
            &mut self.pairs,
            &self.right_states,
            &mut self.builder,
        );
        if is_new {
            self.agenda.push_back((rule.result, root_right, parent));
        }
        self.rule_tracker.add_rule(
            &mut self.builder,
            rule.symbol,
            product_children,
            parent,
            rule.weight,
        );
    }
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
    let mut program_by_term = vec![None; hom.num_terms()];
    let mut rules = Vec::<OwnedRule>::new();
    let mut rule_programs = Vec::<usize>::new();

    for rule in left.rules() {
        let Some(term_id) = hom.term_id(rule.symbol) else {
            continue;
        };
        let program = if let Some(program) = program_by_term[term_id] {
            program
        } else {
            let program = programs.len();
            programs.push(compile_term(
                hom.arena(),
                hom.term_by_id(term_id),
                rule.children.len(),
            )?);
            program_by_term[term_id] = Some(program);
            program
        };
        debug_assert_eq!(programs[program].arity(), rule.children.len());
        rules.push(OwnedRule {
            symbol: rule.symbol,
            children: rule.children.iter().copied().collect(),
            result: rule.result,
            weight: rule.weight,
        });
        rule_programs.push(program);
    }

    let mut program_left_indexes: Vec<SetTrie<StateId, Vec<usize>>> =
        (0..programs.len()).map(|_| SetTrie::new()).collect();
    let mut by_left_child: Vec<Vec<OccurrenceGroup>> =
        (0..left.num_states()).map(|_| Vec::new()).collect();
    let mut occurrence_group_ids: Vec<FxHashMap<(usize, usize), usize>> = (0..left.num_states())
        .map(|_| FxHashMap::default())
        .collect();
    for (rule_id, rule) in rules.iter().enumerate() {
        let program = rule_programs[rule_id];
        program_left_indexes[program]
            .get_or_insert_with(&rule.children, Vec::new)
            .push(rule_id);
        for (position, &child) in rule.children.iter().enumerate() {
            let groups = &mut by_left_child[child.index()];
            let group_ids = &mut occurrence_group_ids[child.index()];
            let group_id = *group_ids.entry((program, position)).or_insert_with(|| {
                let group_id = groups.len();
                groups.push(OccurrenceGroup {
                    program,
                    position,
                    rule_ids: Vec::new(),
                });
                group_id
            });
            groups[group_id].rule_ids.push(rule_id);
        }
    }
    drop(occurrence_group_ids);

    let mut charts: Vec<RhsChart<D::Key>> = programs.iter().map(RhsChart::new).collect();
    let mut intersection = SiblingIntersection::new(left, decomp);
    let mut new_roots = Vec::<usize>::new();
    let mut candidate_rules = Vec::<usize>::new();
    let mut activation_slots = Vec::<(usize, usize, usize)>::new();

    for program in 0..programs.len() {
        if programs[program].arity() != 0 {
            continue;
        }
        new_roots.clear();
        let mut evaluation = RhsEvaluation {
            decomp,
            right_states: &mut intersection.right_states,
            stats: &mut intersection.stats,
            control,
        };
        charts[program].initialize(&programs[program], &mut evaluation, &mut new_roots)?;
        for root_id in new_roots.drain(..) {
            charts[program].mark_root_born(root_id, intersection.pairs.len());
            let (root_right, root_children) = charts[program].root(root_id);
            program_left_indexes[program].for_each_value_for_key_sets(
                &[] as &[ProductLeftSet<'_>],
                |candidate_rules| {
                    for &rule_id in candidate_rules {
                        intersection.emit(&rules[rule_id], root_right, root_children, None);
                    }
                },
            );
        }
    }

    while let Some((left_state, right_state, product)) = intersection.agenda.pop_front() {
        control.check()?;
        intersection.stats.agenda_pops += 1;
        let occurrence_groups = &by_left_child[left_state.index()];
        activation_slots.clear();
        for group in occurrence_groups {
            let root_count = charts[group.program]
                .roots_with_child(group.position, right_state)
                .len();
            activation_slots.push((group.program, group.position, root_count));
        }

        for &(program, position, _) in &activation_slots {
            new_roots.clear();
            let mut evaluation = RhsEvaluation {
                decomp,
                right_states: &mut intersection.right_states,
                stats: &mut intersection.stats,
                control,
            };
            charts[program].activate(
                &programs[program],
                position,
                right_state,
                &mut evaluation,
                &mut new_roots,
            )?;

            for root_id in new_roots.drain(..) {
                charts[program].mark_root_born(root_id, intersection.pairs.len());
                let (root_right, root_children) = charts[program].root(root_id);
                let mut child_sets = SmallVec::<[ProductLeftSet<'_>; 4]>::new();
                let mut complete = true;
                for child in root_children {
                    if let Some(row) = intersection.products.left_partners(*child) {
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
                    intersection.emit(&rules[candidate], root_right, root_children, None);
                }
            }
        }

        for (group, &(_, _, root_count)) in occurrence_groups.iter().zip(&activation_slots) {
            let program = group.program;
            let position = group.position;
            for index in 0..root_count {
                let root_id = charts[program].roots_with_child(position, right_state)[index];
                let (root_right, root_children) = charts[program].root(root_id);
                let root_birth = charts[program].root_birth(root_id);
                for &rule_id in &group.rule_ids {
                    intersection.emit(
                        &rules[rule_id],
                        root_right,
                        root_children,
                        Some((position, product, root_birth)),
                    );
                }
            }
        }
    }

    intersection.stats.output_states = intersection.pairs.len();
    let chart = intersection.builder.build_trusted();
    intersection.stats.output_rules = chart.rules().count();
    Ok((
        chart,
        intersection.right_states,
        intersection.pairs,
        intersection.stats,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assignments_use_node_local_width_and_participate_in_item_identity() {
        let plan = CompiledTerm {
            nodes: vec![
                NodePlan {
                    parent: None,
                    operation: None,
                    assignment_width: 1,
                },
                NodePlan {
                    parent: None,
                    operation: None,
                    assignment_width: 3,
                },
            ],
            variable_nodes: Vec::new(),
            root_permutation: SmallVec::new(),
        };
        let mut chart = RhsChart::<usize>::new(&plan);
        let mut stats = SiblingIntersectionStats::default();
        let first = [StateId(0), StateId(1), StateId(2)];
        let second = [StateId(0), StateId(1), StateId(3)];

        chart.insert(0, StateId(7), &[StateId(1)], &mut stats);
        chart.insert(1, StateId(7), &first, &mut stats);
        chart.insert(1, StateId(7), &first, &mut stats);
        chart.insert(1, StateId(7), &second, &mut stats);

        assert_eq!(chart.nodes[0].assignments.len(), 1);
        assert_eq!(chart.nodes[1].items.len(), 2);
        assert_eq!(chart.nodes[1].assignments.len(), 6);
        assert_eq!(chart.assignment(1, 0), first);
        assert_eq!(chart.assignment(1, 1), second);
        assert_eq!(stats.term_items, 3);
    }

    #[test]
    fn root_assignment_is_reordered_without_per_item_storage() {
        let mut assignment = Vec::new();
        merge_assignments_into(
            &[StateId(10), StateId(20)],
            &[StateId(30)],
            &[2, 0, 1],
            &mut assignment,
        );
        assert_eq!(assignment, [StateId(30), StateId(10), StateId(20)]);

        copy_assignment_into(
            &[StateId(10), StateId(20), StateId(30)],
            &[2, 0, 1],
            &mut assignment,
        );
        assert_eq!(assignment, [StateId(30), StateId(10), StateId(20)]);
    }

    #[test]
    fn compilation_records_only_a_root_permutation() {
        let mut arena = TreeArena::new();
        let variable_one = arena.add_node(HomLabel::Var(1), Vec::new());
        let variable_zero = arena.add_node(HomLabel::Var(0), Vec::new());
        let root = arena.add_node(
            HomLabel::Symbol(Symbol(0)),
            vec![variable_one, variable_zero],
        );

        let plan = compile_term(&arena, root, 2).unwrap();

        assert_eq!(plan.root_permutation.as_slice(), [1, 0]);
        assert_eq!(plan.nodes[plan.variable_nodes[1]].assignment_width, 1);
        assert_eq!(plan.nodes[plan.variable_nodes[0]].assignment_width, 1);
        assert_eq!(plan.nodes[ROOT_NODE].assignment_width, 2);
    }
}
