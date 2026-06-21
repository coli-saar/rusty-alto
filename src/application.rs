//! Stable, owned presentation types for desktop and web frontends.
//!
//! The core algorithms deliberately expose compact IDs and borrowed trees.
//! Frontends usually need the inverse trade-off: resolved names and owned
//! values that can safely cross worker-thread and event-loop boundaries.

use crate::{
    AstarHeuristic, AstarOptions, BottomUpTa, Explicit, Irtg, IrtgError, MaterializationStrategy,
    StateId, Symbol, TreeValue,
};
use packed_term_arena::{
    parser::parse_tree,
    tree::{Tree, TreeArena},
};

/// A read-only summary of an explicit automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AutomatonSummary {
    /// Number of transition rules.
    pub rule_count: usize,
    /// Number of allocated states.
    pub state_count: u32,
    /// Largest child count of any rule.
    pub maximum_rank: usize,
    /// Whether the accepted language is empty.
    pub is_empty: bool,
}

/// Cardinality of an explicit automaton's derivation-tree language.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LanguageCardinality {
    /// The language contains exactly this many derivation trees.
    Finite(usize),
    /// A productive cycle makes the language infinite.
    Infinite,
    /// The finite count exceeds the platform's `usize` range.
    TooLarge,
}

/// Metadata about one interpretation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterpretationInfo {
    /// Interpretation name used in grammar and corpus files.
    pub name: String,
    /// Declared Alto algebra class name.
    pub class_name: String,
    /// Whether this interpretation can constrain parsing input.
    pub input_capable: bool,
}

/// One resolved automaton rule suitable for tables and serialization.
#[derive(Clone, Debug, PartialEq)]
pub struct ResolvedRule {
    /// Human-readable parent state.
    pub parent: String,
    /// Whether the parent state is accepting.
    pub parent_is_final: bool,
    /// Human-readable rule symbol.
    pub symbol: String,
    /// Human-readable child states in order.
    pub children: Vec<String>,
    /// Rule weight.
    pub weight: f64,
    /// Homomorphic image term for each interpretation.
    pub interpretation_terms: Vec<(String, String)>,
}

/// An owned interpretation result.
#[derive(Debug)]
pub enum RenderedValue {
    /// A scalar or otherwise non-tree textual value.
    Text(String),
    /// A structured tree value retaining its arena.
    Tree(TreeValue),
}

/// One named result of interpreting a derivation.
#[derive(Debug)]
pub struct RenderedInterpretation {
    /// Interpretation name.
    pub name: String,
    /// Evaluated value.
    pub value: RenderedValue,
}

/// Frontend-friendly parsing strategy without borrowed heuristic tables.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ParseStrategy {
    /// Parent-driven condensed intersection.
    TopDownCondensed,
    /// Child-indexed condensed intersection.
    IndexedCondensed,
    /// Generic A* with the zero heuristic.
    AstarZero {
        /// Stop once the highest-ranked complete derivation is found.
        stop_at_first_goal: bool,
        /// Optional merit threshold.
        beam: Option<f64>,
    },
}

impl ParseStrategy {
    /// Convert this owned frontend choice into the core strategy type.
    pub fn materialization_strategy(&self) -> MaterializationStrategy<'static> {
        match *self {
            Self::TopDownCondensed => MaterializationStrategy::TopDownCondensed,
            Self::IndexedCondensed => MaterializationStrategy::IndexedCondensed,
            Self::AstarZero {
                stop_at_first_goal,
                beam,
            } => MaterializationStrategy::Astar {
                heuristic: AstarHeuristic::Zero,
                options: AstarOptions {
                    stop_at_first_goal,
                    beam,
                },
            },
        }
    }
}

impl Explicit {
    /// Return an owned summary without exposing internal indexes.
    pub fn application_summary(&self) -> AutomatonSummary {
        AutomatonSummary {
            rule_count: self.rules().count(),
            state_count: self.num_states(),
            maximum_rank: self
                .rules()
                .map(|rule| rule.children.len())
                .max()
                .unwrap_or(0),
            is_empty: self.is_empty(),
        }
    }

    /// Return the number of accepted derivation trees without enumerating them.
    pub fn language_cardinality(&self) -> LanguageCardinality {
        let state_count = self.num_states() as usize;
        let rules = self.rules().collect::<Vec<_>>();
        let mut productive = vec![false; state_count];
        let mut changed = true;
        while changed {
            changed = false;
            for rule in &rules {
                if !productive[rule.result.index()]
                    && rule.children.iter().all(|child| productive[child.index()])
                {
                    productive[rule.result.index()] = true;
                    changed = true;
                }
            }
        }

        let mut relevant = vec![false; state_count];
        let mut stack = (0..state_count)
            .map(|index| StateId(index as u32))
            .filter(|state| self.is_accepting(state) && productive[state.index()])
            .collect::<Vec<_>>();
        while let Some(state) = stack.pop() {
            if std::mem::replace(&mut relevant[state.index()], true) {
                continue;
            }
            for rule in rules.iter().filter(|rule| rule.result == state) {
                if rule.children.iter().all(|child| productive[child.index()]) {
                    stack.extend(rule.children.iter().copied());
                }
            }
        }

        fn has_cycle(
            state: StateId,
            rules: &[crate::Rule<'_>],
            productive: &[bool],
            relevant: &[bool],
            colors: &mut [u8],
        ) -> bool {
            colors[state.index()] = 1;
            for child in rules
                .iter()
                .filter(|rule| {
                    rule.result == state
                        && rule.children.iter().all(|child| productive[child.index()])
                })
                .flat_map(|rule| rule.children.iter().copied())
                .filter(|child| relevant[child.index()])
            {
                if colors[child.index()] == 1
                    || (colors[child.index()] == 0
                        && has_cycle(child, rules, productive, relevant, colors))
                {
                    return true;
                }
            }
            colors[state.index()] = 2;
            false
        }

        let mut colors = vec![0; state_count];
        for index in 0..state_count {
            if relevant[index]
                && colors[index] == 0
                && has_cycle(
                    StateId(index as u32),
                    &rules,
                    &productive,
                    &relevant,
                    &mut colors,
                )
            {
                return LanguageCardinality::Infinite;
            }
        }

        fn count_state(
            state: StateId,
            rules: &[crate::Rule<'_>],
            productive: &[bool],
            memo: &mut [Option<Option<usize>>],
        ) -> Option<usize> {
            if let Some(count) = memo[state.index()] {
                return count;
            }
            let mut total = 0usize;
            for rule in rules.iter().filter(|rule| {
                rule.result == state && rule.children.iter().all(|child| productive[child.index()])
            }) {
                let mut combinations = 1usize;
                for &child in rule.children {
                    combinations =
                        combinations.checked_mul(count_state(child, rules, productive, memo)?)?;
                }
                total = total.checked_add(combinations)?;
            }
            memo[state.index()] = Some(Some(total));
            Some(total)
        }

        let mut memo = vec![None; state_count];
        let mut total = 0usize;
        for index in 0..state_count {
            let state = StateId(index as u32);
            if self.is_accepting(&state) && productive[index] {
                let Some(count) = count_state(state, &rules, &productive, &mut memo) else {
                    return LanguageCardinality::TooLarge;
                };
                let Some(next) = total.checked_add(count) else {
                    return LanguageCardinality::TooLarge;
                };
                total = next;
            }
        }
        LanguageCardinality::Finite(total)
    }

    /// Resolve rules with caller-supplied state and symbol naming.
    pub fn resolve_rules(
        &self,
        mut state_name: impl FnMut(StateId) -> String,
        mut symbol_name: impl FnMut(Symbol) -> String,
    ) -> Vec<ResolvedRule> {
        self.rules()
            .map(|rule| ResolvedRule {
                parent: state_name(rule.result),
                parent_is_final: self.is_accepting(&rule.result),
                symbol: symbol_name(rule.symbol),
                children: rule.children.iter().copied().map(&mut state_name).collect(),
                weight: rule.weight,
                interpretation_terms: Vec::new(),
            })
            .collect()
    }

    /// Resolve a single rule by index with caller-supplied naming.
    pub fn resolved_rule(
        &self,
        index: usize,
        mut state_name: impl FnMut(StateId) -> String,
        mut symbol_name: impl FnMut(Symbol) -> String,
    ) -> ResolvedRule {
        let rule = self.rule(index);
        ResolvedRule {
            parent: state_name(rule.result),
            parent_is_final: self.is_accepting(&rule.result),
            symbol: symbol_name(rule.symbol),
            children: rule.children.iter().copied().map(&mut state_name).collect(),
            weight: rule.weight,
            interpretation_terms: Vec::new(),
        }
    }
}

impl Irtg {
    /// Return sorted interpretation metadata for deterministic presentation.
    pub fn interpretation_info(&self) -> Vec<InterpretationInfo> {
        let mut values: Vec<_> = self
            .interpretations()
            .map(|interpretation| InterpretationInfo {
                name: interpretation.name().to_owned(),
                class_name: interpretation.class_name().to_owned(),
                input_capable: interpretation.is_inputable(),
            })
            .collect();
        values.sort_by(|a, b| a.name.cmp(&b.name));
        values
    }

    /// Resolve grammar rules, including each interpretation's homomorphic term.
    pub fn resolved_grammar_rules(&self) -> Vec<ResolvedRule> {
        let mut interpretations: Vec<_> = self.interpretations().collect();
        interpretations.sort_by_key(|interpretation| interpretation.name());

        self.grammar()
            .rules()
            .map(|rule| {
                let interpretation_terms = interpretations
                    .iter()
                    .map(|interpretation| {
                        let text = interpretation
                            .homomorphism()
                            .get(rule.symbol)
                            .map(|root| {
                                format_hom_term(
                                    interpretation.homomorphism().arena(),
                                    root,
                                    interpretation.algebra_signature(),
                                )
                            })
                            .unwrap_or_default();
                        (interpretation.name().to_owned(), text)
                    })
                    .collect();

                ResolvedRule {
                    parent: self.states().resolve(rule.result).clone(),
                    parent_is_final: self.grammar().is_accepting(&rule.result),
                    symbol: self.grammar_signature().resolve(rule.symbol).to_owned(),
                    children: rule
                        .children
                        .iter()
                        .map(|&state| self.states().resolve(state).clone())
                        .collect(),
                    weight: rule.weight,
                    interpretation_terms,
                }
            })
            .collect()
    }

    /// Number of grammar rules.
    pub fn num_grammar_rules(&self) -> usize {
        self.grammar().num_rules()
    }

    /// Resolve a single grammar rule by index, including interpretation terms.
    ///
    /// Intended for on-demand, per-row resolution (e.g. a virtualized table).
    /// To resolve every rule, prefer [`Self::resolved_grammar_rules`], which
    /// sorts interpretations once instead of per call.
    pub fn resolved_grammar_rule(&self, index: usize) -> ResolvedRule {
        let mut interpretations: Vec<_> = self.interpretations().collect();
        interpretations.sort_by_key(|interpretation| interpretation.name());

        let rule = self.grammar().rule(index);
        let interpretation_terms = interpretations
            .iter()
            .map(|interpretation| {
                let text = interpretation
                    .homomorphism()
                    .get(rule.symbol)
                    .map(|root| {
                        format_hom_term(
                            interpretation.homomorphism().arena(),
                            root,
                            interpretation.algebra_signature(),
                        )
                    })
                    .unwrap_or_default();
                (interpretation.name().to_owned(), text)
            })
            .collect();

        ResolvedRule {
            parent: self.states().resolve(rule.result).clone(),
            parent_is_final: self.grammar().is_accepting(&rule.result),
            symbol: self.grammar_signature().resolve(rule.symbol).to_owned(),
            children: rule
                .children
                .iter()
                .map(|&state| self.states().resolve(state).clone())
                .collect(),
            weight: rule.weight,
            interpretation_terms,
        }
    }

    /// Resolve a derivation tree to an owned string-labelled tree.
    pub fn resolve_derivation(&self, arena: &TreeArena<Symbol>, root: Tree) -> TreeValue {
        let (arena, root) = self.grammar_signature().resolve_tree(arena, root);
        TreeValue::new(arena, root)
    }

    /// Evaluate all interpretations and retain tree structure where available.
    pub fn render_derivation(
        &self,
        arena: &TreeArena<Symbol>,
        root: Tree,
    ) -> Result<Vec<RenderedInterpretation>, IrtgError> {
        let mut interpretations: Vec<_> = self.interpretations().collect();
        interpretations.sort_by_key(|interpretation| interpretation.name());

        interpretations
            .into_iter()
            .map(|interpretation| {
                let text = interpretation.interpret_to_string(arena, root)?;
                let value = if interpretation.is_tree_valued() {
                    let mut tree_arena = TreeArena::new();
                    match parse_tree(&mut tree_arena, &text) {
                        Ok(tree_root) => RenderedValue::Tree(TreeValue::new(tree_arena, tree_root)),
                        Err(_) => RenderedValue::Text(text),
                    }
                } else {
                    RenderedValue::Text(text)
                };
                Ok(RenderedInterpretation {
                    name: interpretation.name().to_owned(),
                    value,
                })
            })
            .collect()
    }
}

fn format_hom_term(
    arena: &TreeArena<crate::HomLabel>,
    node: Tree,
    signature: &crate::Signature,
) -> String {
    let label = match arena.get_label(node) {
        crate::HomLabel::Symbol(symbol) => signature.resolve(*symbol).to_owned(),
        crate::HomLabel::Var(index) => format!("?{}", index + 1),
    };
    let children = arena.get_children(node);
    if children.is_empty() {
        label
    } else {
        let children = children
            .iter()
            .map(|&child| format_hom_term(arena, child, signature))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{label}({children})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_irtg;

    const GRAMMAR: &str = r#"
interpretation string: de.up.ling.irtg.algebra.StringAlgebra
interpretation tree: de.up.ling.irtg.algebra.TreeWithAritiesAlgebra

S! -> r(NP, VP) [0.7]
  [string] *(?1, ?2)
  [tree] S_2(?1, ?2)

NP -> john [1.0]
  [string] john
  [tree] John_0

VP -> sleeps [1.0]
  [string] sleeps
  [tree] sleeps_0
"#;

    #[test]
    fn resolves_single_explicit_rule() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let g = irtg.grammar();
        let all = g.resolve_rules(
            |s| format!("q{}", s.index()),
            |sym| irtg.grammar_signature().resolve(sym).to_owned(),
        );
        for i in 0..g.num_rules() {
            let one = g.resolved_rule(
                i,
                |s| format!("q{}", s.index()),
                |sym| irtg.grammar_signature().resolve(sym).to_owned(),
            );
            assert_eq!(one, all[i]);
        }
    }

    #[test]
    fn resolves_application_records() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let summary = irtg.grammar().application_summary();
        assert_eq!(summary.rule_count, 3);
        assert_eq!(summary.maximum_rank, 2);
        let rules = irtg.resolved_grammar_rules();
        assert_eq!(rules[0].parent, "S");
        assert!(rules[0].parent_is_final);
        assert_eq!(rules[0].interpretation_terms[0].0, "string");
    }

    #[test]
    fn strategy_conversion_is_stable() {
        assert!(matches!(
            ParseStrategy::IndexedCondensed.materialization_strategy(),
            MaterializationStrategy::IndexedCondensed
        ));
        let strategy = ParseStrategy::AstarZero {
            stop_at_first_goal: true,
            beam: Some(0.2),
        }
        .materialization_strategy();
        assert!(matches!(strategy, MaterializationStrategy::Astar { .. }));
    }

    #[test]
    fn resolves_single_grammar_rule() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let all = irtg.resolved_grammar_rules();
        assert_eq!(irtg.num_grammar_rules(), all.len());
        for i in 0..irtg.num_grammar_rules() {
            assert_eq!(irtg.resolved_grammar_rule(i), all[i]);
        }
    }

    #[test]
    fn preserves_tree_results() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let string = irtg
            .interpretation_ref("string")
            .unwrap()
            .parse_object_erased("john sleeps")
            .unwrap();
        let chart = irtg
            .parse([irtg
                .interpretation_ref("string")
                .unwrap()
                .input_erased(string)])
            .unwrap();
        assert!(chart.state_names.iter().any(|name| name == "NP[0,1]"));
        assert!(chart.state_names.iter().any(|name| name == "VP[1,2]"));
        assert!(chart.state_names.iter().any(|name| name == "S[0,2]"));
        let best = chart.automaton.viterbi().unwrap();
        let rendered = irtg.render_derivation(best.arena(), best.root()).unwrap();
        assert!(matches!(rendered[0].value, RenderedValue::Text(_)));
        assert!(matches!(rendered[1].value, RenderedValue::Tree(_)));
    }

    #[test]
    fn reports_finite_and_infinite_language_cardinality() {
        let finite = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        assert_eq!(
            finite.grammar().language_cardinality(),
            LanguageCardinality::Finite(1)
        );

        let recursive = parse_irtg(
            br#"
            interpretation string: de.up.ling.irtg.algebra.StringAlgebra

            S! -> wrap(S)
              [string] *(x, ?1)
            S -> leaf
              [string] x
            "# as &[u8],
        )
        .unwrap();
        assert_eq!(
            recursive.grammar().language_cardinality(),
            LanguageCardinality::Infinite
        );
    }
}
