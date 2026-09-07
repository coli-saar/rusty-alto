use crate::{BottomUpTa, Explicit, StateId};
use std::collections::VecDeque;

pub(crate) struct RuleInput<'a> {
    pub(crate) children: &'a [StateId],
    pub(crate) result: StateId,
}

pub(crate) struct LanguageAnalysis {
    pub(crate) productive: Vec<bool>,
    pub(crate) productive_rules: Vec<bool>,
    pub(crate) relevant: Vec<bool>,
    pub(crate) rules_by_result: Vec<Vec<usize>>,
    /// Child-before-parent order, or `None` when the relevant graph is cyclic.
    pub(crate) topological: Option<Vec<StateId>>,
}

pub(crate) fn explicit_rule_inputs(automaton: &Explicit) -> Vec<RuleInput<'_>> {
    automaton
        .rules()
        .map(|rule| RuleInput {
            children: rule.children,
            result: rule.result,
        })
        .collect()
}

pub(crate) fn analyze_explicit(automaton: &Explicit) -> LanguageAnalysis {
    let inputs = explicit_rule_inputs(automaton);
    let accepting = (0..automaton.num_states())
        .map(StateId)
        .filter(|state| automaton.is_accepting(state));
    analyze(automaton.num_states() as usize, &inputs, accepting)
}

pub(crate) fn analyze(
    state_count: usize,
    rules: &[RuleInput<'_>],
    accepting: impl IntoIterator<Item = StateId>,
) -> LanguageAnalysis {
    let mut productive = vec![false; state_count];
    let mut productive_rules = vec![false; rules.len()];
    let mut remaining = Vec::with_capacity(rules.len());
    let mut occurrences = vec![Vec::new(); state_count];
    let mut rules_by_result = vec![Vec::new(); state_count];
    let mut work = VecDeque::new();

    for (rule_index, rule) in rules.iter().enumerate() {
        remaining.push(rule.children.len());
        rules_by_result[rule.result.index()].push(rule_index);
        if rule.children.is_empty() {
            productive_rules[rule_index] = true;
            if !productive[rule.result.index()] {
                productive[rule.result.index()] = true;
                work.push_back(rule.result);
            }
        } else {
            for &child in rule.children {
                occurrences[child.index()].push(rule_index);
            }
        }
    }

    while let Some(state) = work.pop_front() {
        for &rule_index in &occurrences[state.index()] {
            remaining[rule_index] -= 1;
            if remaining[rule_index] == 0 {
                productive_rules[rule_index] = true;
                let result = rules[rule_index].result;
                if !productive[result.index()] {
                    productive[result.index()] = true;
                    work.push_back(result);
                }
            }
        }
    }

    let accepting = accepting.into_iter().collect::<Vec<_>>();
    let mut relevant = vec![false; state_count];
    let mut stack = accepting
        .iter()
        .copied()
        .filter(|state| productive[state.index()])
        .collect::<Vec<_>>();
    while let Some(state) = stack.pop() {
        if std::mem::replace(&mut relevant[state.index()], true) {
            continue;
        }
        for &rule_index in &rules_by_result[state.index()] {
            if productive_rules[rule_index] {
                stack.extend(rules[rule_index].children.iter().copied());
            }
        }
    }

    // Edges point from a child dependency to its parent. Kahn's algorithm then
    // yields exactly the order needed by bottom-up dynamic programs.
    let mut dependency_count = vec![0usize; state_count];
    let mut dependents = vec![Vec::new(); state_count];
    for (rule_index, rule) in rules.iter().enumerate() {
        if !productive_rules[rule_index] || !relevant[rule.result.index()] {
            continue;
        }
        for &child in rule.children {
            dependency_count[rule.result.index()] += 1;
            dependents[child.index()].push(rule.result);
        }
    }

    let relevant_count = relevant.iter().filter(|&&value| value).count();
    let mut ready = (0..state_count)
        .filter(|&index| relevant[index] && dependency_count[index] == 0)
        .map(|index| StateId(index as u32))
        .collect::<VecDeque<_>>();
    let mut order = Vec::with_capacity(relevant_count);
    while let Some(state) = ready.pop_front() {
        order.push(state);
        for &parent in &dependents[state.index()] {
            dependency_count[parent.index()] -= 1;
            if dependency_count[parent.index()] == 0 {
                ready.push_back(parent);
            }
        }
    }

    LanguageAnalysis {
        productive,
        productive_rules,
        relevant,
        rules_by_result,
        topological: (order.len() == relevant_count).then_some(order),
    }
}
