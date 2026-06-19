//! Fast EVALB-style Parseval scoring for constituency trees.

use crate::{FxHashMap, FxHashSet};
use packed_term_arena::tree::{Tree, TreeArena};
use smallvec::SmallVec;
use std::{error::Error, fmt};

/// The conventional Collins/PTB EVALB profile used when no parameter file is supplied.
const COLLINS_PTB_PARAMS: &str = r#"
CUTOFF_LEN 40
DELETE_LABEL TOP
DELETE_LABEL S1
DELETE_LABEL ROOT
DELETE_LABEL -NONE-
DELETE_LABEL ,
DELETE_LABEL :
DELETE_LABEL ``
DELETE_LABEL ''
DELETE_LABEL .
DELETE_LABEL ?
DELETE_LABEL !
DELETE_LABEL -LRB-
DELETE_LABEL -RRB-
DELETE_LABEL $
DELETE_LABEL #
DELETE_LABEL AUX
DELETE_LABEL AUXG
EQ_LABEL ADVP PRT
"#;

/// EVALB normalization parameters relevant to constituent scoring.
#[derive(Clone, Debug, Default)]
pub struct EvalbParams {
    delete_labels: FxHashSet<String>,
    delete_words: FxHashSet<String>,
    equivalent_labels: FxHashMap<String, String>,
    cutoff_len: Option<usize>,
}

impl EvalbParams {
    /// Parse an EVALB parameter file.
    pub fn parse(input: &str) -> Result<Self, EvalbParamError> {
        let mut params = Self::default();
        for (line_index, raw_line) in input.lines().enumerate() {
            let line_no = line_index + 1;
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            let fields: Vec<&str> = line.split_whitespace().collect();
            match fields.as_slice() {
                ["DELETE_LABEL", labels @ ..] if !labels.is_empty() => {
                    params
                        .delete_labels
                        .extend(labels.iter().map(|label| (*label).to_owned()));
                }
                ["DELETE_WORD", words @ ..] if !words.is_empty() => {
                    params
                        .delete_words
                        .extend(words.iter().map(|word| (*word).to_owned()));
                }
                ["EQ_LABEL", left, right] => {
                    params.add_label_equivalence(left, right);
                }
                ["CUTOFF_LEN", value] => {
                    params.cutoff_len = Some(value.parse().map_err(|_| {
                        EvalbParamError::new(line_no, format!("invalid CUTOFF_LEN value {value:?}"))
                    })?);
                }
                // These standard EVALB controls do not affect the bracket inventory.
                ["DEBUG", _]
                | ["MAX_ERROR", _]
                | ["LABELED", _]
                | ["DISC_ONLY", _]
                | ["TREE_PAIR", _] => {}
                [directive, ..] => {
                    return Err(EvalbParamError::new(
                        line_no,
                        format!("unsupported or malformed directive {directive:?}"),
                    ));
                }
                [] => unreachable!(),
            }
        }
        Ok(params)
    }

    /// Return the built-in Collins/PTB normalization profile.
    pub fn collins_ptb() -> Self {
        Self::parse(COLLINS_PTB_PARAMS).expect("embedded EVALB parameters are valid")
    }

    /// Maximum normalized sentence length to score, if configured.
    pub fn cutoff_len(&self) -> Option<usize> {
        self.cutoff_len
    }

    fn add_label_equivalence(&mut self, left: &str, right: &str) {
        let left_canonical = self
            .equivalent_labels
            .get(left)
            .cloned()
            .unwrap_or_else(|| left.to_owned());
        let right_canonical = self
            .equivalent_labels
            .get(right)
            .cloned()
            .unwrap_or_else(|| right.to_owned());
        let canonical = left_canonical.clone();
        for mapped in self.equivalent_labels.values_mut() {
            if *mapped == right_canonical {
                *mapped = canonical.clone();
            }
        }
        self.equivalent_labels
            .insert(left.to_owned(), canonical.clone());
        self.equivalent_labels.insert(right.to_owned(), canonical);
    }

    fn canonical_label<'a>(&'a self, label: &'a str) -> &'a str {
        self.equivalent_labels
            .get(label)
            .map_or(label, String::as_str)
    }
}

/// A line-numbered EVALB parameter error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalbParamError {
    line: usize,
    message: String,
}

impl EvalbParamError {
    fn new(line: usize, message: String) -> Self {
        Self { line, message }
    }
}

impl fmt::Display for EvalbParamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl Error for EvalbParamError {}

/// Sufficient statistics for labeled and unlabeled Parseval.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ParsevalCounts {
    /// Number of scored constituents in the predicted tree.
    pub predicted: usize,
    /// Number of scored constituents in the gold tree.
    pub gold: usize,
    /// Number of matching labeled constituents.
    pub matched_labeled: usize,
    /// Number of matching unlabeled constituents.
    pub matched_unlabeled: usize,
}

impl ParsevalCounts {
    /// Add another sentence's counts.
    pub fn add_assign(&mut self, other: Self) {
        self.predicted += other.predicted;
        self.gold += other.gold;
        self.matched_labeled += other.matched_labeled;
        self.matched_unlabeled += other.matched_unlabeled;
    }

    /// Labeled precision.
    pub fn labeled_precision(self) -> f64 {
        ratio(self.matched_labeled, self.predicted)
    }

    /// Labeled recall.
    pub fn labeled_recall(self) -> f64 {
        ratio(self.matched_labeled, self.gold)
    }

    /// Labeled F1.
    pub fn labeled_f1(self) -> f64 {
        f1(self.labeled_precision(), self.labeled_recall())
    }

    /// Unlabeled precision.
    pub fn unlabeled_precision(self) -> f64 {
        ratio(self.matched_unlabeled, self.predicted)
    }

    /// Unlabeled recall.
    pub fn unlabeled_recall(self) -> f64 {
        ratio(self.matched_unlabeled, self.gold)
    }

    /// Unlabeled F1.
    pub fn unlabeled_f1(self) -> f64 {
        f1(self.unlabeled_precision(), self.unlabeled_recall())
    }
}

fn ratio(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        1.0
    } else {
        numerator as f64 / denominator as f64
    }
}

fn f1(precision: f64, recall: f64) -> f64 {
    if precision + recall == 0.0 {
        0.0
    } else {
        2.0 * precision * recall / (precision + recall)
    }
}

/// Why a sentence was not scored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParsevalSkip {
    /// Gold and predicted trees have different normalized terminal counts.
    LengthMismatch {
        /// Predicted normalized terminal count.
        predicted: usize,
        /// Gold normalized terminal count.
        gold: usize,
    },
    /// The normalized gold sentence exceeds `CUTOFF_LEN`.
    Cutoff {
        /// Gold normalized terminal count.
        length: usize,
        /// Configured cutoff.
        cutoff: usize,
    },
}

/// Compare two constituency trees after EVALB normalization.
///
/// Both trees are traversed and merged lazily in left-to-right postorder. Expected running time
/// is linear in the two tree sizes; auxiliary memory is proportional to tree depth plus the
/// largest group of constituents sharing one span.
pub fn compare_trees(
    predicted_arena: &TreeArena<String>,
    predicted_root: Tree,
    gold_arena: &TreeArena<String>,
    gold_root: Tree,
    params: &EvalbParams,
) -> Result<ParsevalCounts, ParsevalSkip> {
    let mut predicted = ConstituentIter::new(predicted_arena, predicted_root, params);
    let mut gold = ConstituentIter::new(gold_arena, gold_root, params);
    let counts = match_constituents(&mut predicted, &mut gold);

    if predicted.words != gold.words {
        return Err(ParsevalSkip::LengthMismatch {
            predicted: predicted.words,
            gold: gold.words,
        });
    }
    if let Some(cutoff) = params.cutoff_len
        && gold.words > cutoff
    {
        return Err(ParsevalSkip::Cutoff {
            length: gold.words,
            cutoff,
        });
    }

    Ok(counts)
}

/// Count gold constituents for a failed parse, applying the cutoff if configured.
pub fn count_gold(
    gold_arena: &TreeArena<String>,
    gold_root: Tree,
    params: &EvalbParams,
) -> Result<ParsevalCounts, ParsevalSkip> {
    let mut gold = ConstituentIter::new(gold_arena, gold_root, params);
    let gold_count = gold.by_ref().count();
    if let Some(cutoff) = params.cutoff_len
        && gold.words > cutoff
    {
        return Err(ParsevalSkip::Cutoff {
            length: gold.words,
            cutoff,
        });
    }
    Ok(ParsevalCounts {
        gold: gold_count,
        ..ParsevalCounts::default()
    })
}

#[derive(Clone, Copy, Debug)]
struct Constituent<'a> {
    start: usize,
    end: usize,
    label: &'a str,
}

struct ConstituentIter<'a> {
    arena: &'a TreeArena<String>,
    params: &'a EvalbParams,
    stack: Vec<Frame>,
    words: usize,
}

#[derive(Clone, Copy)]
struct Frame {
    node: Tree,
    next_child: usize,
    start: usize,
}

impl<'a> ConstituentIter<'a> {
    fn new(arena: &'a TreeArena<String>, root: Tree, params: &'a EvalbParams) -> Self {
        Self {
            arena,
            params,
            stack: vec![Frame {
                node: root,
                next_child: 0,
                start: 0,
            }],
            words: 0,
        }
    }
}

impl<'a> Iterator for ConstituentIter<'a> {
    type Item = Constituent<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(frame) = self.stack.last_mut() {
            let children = self.arena.get_children(frame.node);
            if frame.next_child < children.len() {
                let child = children[frame.next_child];
                frame.next_child += 1;
                self.stack.push(Frame {
                    node: child,
                    next_child: 0,
                    start: self.words,
                });
                continue;
            }

            let frame = self.stack.pop().expect("stack is nonempty");
            let children = self.arena.get_children(frame.node);
            let label = self.arena.get_label(frame.node).as_str();
            if children.is_empty() {
                let parent_deletes_terminal = self.stack.last().is_some_and(|parent| {
                    self.params
                        .delete_labels
                        .contains(self.arena.get_label(parent.node).as_str())
                });
                // Ordinary PTB trees represent terminals as words below a POS preterminal, so
                // DELETE_LABEL applies to the parent. Alto's TreeWithArities PTB corpora omit
                // words and use the POS tag itself as the leaf, so the same directive must also
                // apply to the leaf label. Supporting both shapes keeps normalization invariant
                // under omission of the word layer.
                let leaf_label_deletes_terminal = self.params.delete_labels.contains(label);
                if !parent_deletes_terminal
                    && !leaf_label_deletes_terminal
                    && !self.params.delete_words.contains(label)
                {
                    self.words += 1;
                }
            } else if !is_preterminal(self.arena, frame.node)
                && self.words > frame.start
                && !self.params.delete_labels.contains(label)
            {
                return Some(Constituent {
                    start: frame.start,
                    end: self.words,
                    label: self.params.canonical_label(label),
                });
            }
        }
        None
    }
}

fn is_preterminal(arena: &TreeArena<String>, node: Tree) -> bool {
    let children = arena.get_children(node);
    children.len() == 1 && arena.get_children(children[0]).is_empty()
}

fn match_constituents(
    predicted: &mut ConstituentIter<'_>,
    gold: &mut ConstituentIter<'_>,
) -> ParsevalCounts {
    let mut counts = ParsevalCounts::default();
    let (mut predicted_item, mut gold_item) = (predicted.next(), gold.next());
    let mut predicted_group: SmallVec<[Constituent<'_>; 8]> = SmallVec::new();
    let mut gold_group: SmallVec<[Constituent<'_>; 8]> = SmallVec::new();

    while let (Some(p), Some(g)) = (predicted_item, gold_item) {
        match span_key(p).cmp(&span_key(g)) {
            std::cmp::Ordering::Less => {
                counts.predicted += 1;
                predicted_item = predicted.next();
                gold_item = Some(g);
            }
            std::cmp::Ordering::Greater => {
                counts.gold += 1;
                gold_item = gold.next();
                predicted_item = Some(p);
            }
            std::cmp::Ordering::Equal => {
                let span = (p.start, p.end);
                predicted_group.clear();
                gold_group.clear();
                predicted_group.push(p);
                gold_group.push(g);

                predicted_item = predicted.next();
                while predicted_item.is_some_and(|item| (item.start, item.end) == span) {
                    predicted_group.push(predicted_item.take().expect("checked Some"));
                    predicted_item = predicted.next();
                }
                gold_item = gold.next();
                while gold_item.is_some_and(|item| (item.start, item.end) == span) {
                    gold_group.push(gold_item.take().expect("checked Some"));
                    gold_item = gold.next();
                }

                counts.predicted += predicted_group.len();
                counts.gold += gold_group.len();
                counts.matched_unlabeled += predicted_group.len().min(gold_group.len());
                counts.matched_labeled +=
                    match_label_multisets(predicted_group.as_slice(), gold_group.as_slice());
            }
        }
    }

    if predicted_item.is_some() {
        counts.predicted += 1;
    }
    if gold_item.is_some() {
        counts.gold += 1;
    }
    counts.predicted += predicted.count();
    counts.gold += gold.count();
    counts
}

fn span_key(item: Constituent<'_>) -> (usize, std::cmp::Reverse<usize>) {
    (item.end, std::cmp::Reverse(item.start))
}

fn match_label_multisets(predicted: &[Constituent<'_>], gold: &[Constituent<'_>]) -> usize {
    if predicted.len().max(gold.len()) <= 8 {
        let mut used = [false; 8];
        let mut matched = 0;
        for p in predicted {
            if let Some(index) = gold
                .iter()
                .enumerate()
                .find_map(|(i, g)| (!used[i] && p.label == g.label).then_some(i))
            {
                used[index] = true;
                matched += 1;
            }
        }
        return matched;
    }

    let mut inventory: FxHashMap<&str, usize> = FxHashMap::default();
    for item in predicted {
        *inventory.entry(item.label).or_default() += 1;
    }
    let mut matched = 0;
    for item in gold {
        if let Some(remaining) = inventory.get_mut(item.label)
            && *remaining > 0
        {
            *remaining -= 1;
            matched += 1;
        }
    }
    matched
}

#[cfg(test)]
mod tests {
    use super::*;
    use packed_term_arena::parser::parse_tree;

    fn tree(text: &str) -> (TreeArena<String>, Tree) {
        let mut arena = TreeArena::new();
        let root = parse_tree(&mut arena, text).unwrap();
        (arena, root)
    }

    fn bare() -> EvalbParams {
        EvalbParams::default()
    }

    #[test]
    fn exact_match_scores_all_constituents() {
        let (a1, r1) = tree("S(NP(DT(the), NN(cat)), VP(VBD(slept)))");
        let (a2, r2) = tree("S(NP(DT(the), NN(cat)), VP(VBD(slept)))");
        let counts = compare_trees(&a1, r1, &a2, r2, &bare()).unwrap();
        assert_eq!(
            counts,
            ParsevalCounts {
                predicted: 3,
                gold: 3,
                matched_labeled: 3,
                matched_unlabeled: 3,
            }
        );
    }

    #[test]
    fn labeled_and_unlabeled_matches_differ() {
        let (pred, pr) = tree("S(X(NN(a), NN(b)))");
        let (gold, gr) = tree("S(NP(NN(a), NN(b)))");
        let counts = compare_trees(&pred, pr, &gold, gr, &bare()).unwrap();
        assert_eq!(counts.matched_unlabeled, 2);
        assert_eq!(counts.matched_labeled, 1);
    }

    #[test]
    fn duplicate_unary_brackets_are_multisets() {
        let (pred, pr) = tree("A(A(A(NN(x))))");
        let (gold, gr) = tree("A(A(NN(x)))");
        let counts = compare_trees(&pred, pr, &gold, gr, &bare()).unwrap();
        assert_eq!(counts.predicted, 3);
        assert_eq!(counts.gold, 2);
        assert_eq!(counts.matched_labeled, 2);
        assert_eq!(counts.matched_unlabeled, 2);
    }

    #[test]
    fn deletion_and_equivalence_normalize_trees() {
        let params =
            EvalbParams::parse("DELETE_LABEL TOP -NONE-\nDELETE_WORD ,\nEQ_LABEL PRT ADVP\n")
                .unwrap();
        let (pred, pr) = tree("TOP(S(PRT(RP(up)), PUNC(',')))");
        let (gold, gr) = tree("S(ADVP(RP(up)))");
        let counts = compare_trees(&pred, pr, &gold, gr, &params).unwrap();
        assert_eq!(counts.matched_labeled, 2);
        assert_eq!(counts.matched_unlabeled, 2);
    }

    #[test]
    fn collins_defaults_delete_root_and_punctuation() {
        let params = EvalbParams::collins_ptb();
        let (pred, pr) = tree("ROOT(S(NP(NN(a)), ','(','), VP(VB(b)), '.'('.')))");
        let (gold, gr) = tree("S(NP(NN(a)), VP(VB(b)))");
        assert_eq!(
            compare_trees(&pred, pr, &gold, gr, &params).unwrap(),
            ParsevalCounts {
                predicted: 3,
                gold: 3,
                matched_labeled: 3,
                matched_unlabeled: 3,
            }
        );
    }

    #[test]
    fn deleted_preterminal_removes_its_terminal_from_spans() {
        let params = EvalbParams::parse("DELETE_LABEL PUNC\n").unwrap();
        let (pred, pr) = tree("S(NP(NN(a)), PUNC(','), VP(VB(b)))");
        let (gold, gr) = tree("S(NP(NN(a)), VP(VB(b)))");
        assert_eq!(
            compare_trees(&pred, pr, &gold, gr, &params).unwrap(),
            ParsevalCounts {
                predicted: 3,
                gold: 3,
                matched_labeled: 3,
                matched_unlabeled: 3,
            }
        );
    }

    #[test]
    fn deleted_pos_leaf_is_removed_in_alto_tree_shape() {
        let params = EvalbParams::collins_ptb();
        let (pred, pr) = tree("S(NP(DT, NN), '.', VP(VB, RB))");
        let (gold, gr) = tree("S(NP(DT, NN), VP(VB, RB))");
        assert_eq!(
            compare_trees(&pred, pr, &gold, gr, &params).unwrap(),
            ParsevalCounts {
                predicted: 3,
                gold: 3,
                matched_labeled: 3,
                matched_unlabeled: 3,
            }
        );
    }

    #[test]
    fn detects_length_mismatch_and_cutoff() {
        let (short, sr) = tree("S(NN(a))");
        let (long, lr) = tree("S(NN(a), NN(b))");
        assert_eq!(
            compare_trees(&short, sr, &long, lr, &bare()),
            Err(ParsevalSkip::LengthMismatch {
                predicted: 1,
                gold: 2
            })
        );

        let params = EvalbParams::parse("CUTOFF_LEN 1").unwrap();
        assert_eq!(
            count_gold(&long, lr, &params),
            Err(ParsevalSkip::Cutoff {
                length: 2,
                cutoff: 1
            })
        );
    }

    #[test]
    fn parameter_errors_include_line_numbers() {
        let error = EvalbParams::parse("DELETE_LABEL TOP\nMYSTERY 1\n").unwrap_err();
        assert_eq!(
            error.to_string(),
            "line 2: unsupported or malformed directive \"MYSTERY\""
        );
    }

    #[test]
    fn empty_denominators_follow_parseval_conventions() {
        let counts = ParsevalCounts::default();
        assert_eq!(counts.labeled_precision(), 1.0);
        assert_eq!(counts.labeled_recall(), 1.0);
        assert_eq!(counts.labeled_f1(), 1.0);
    }
}
