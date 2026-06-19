//! Step 2 of the F-heuristic plan (`docs/f-heuristic-design.md`): predicted-pruning probe.
//!
//! K&M's finalization predictor: an A* search with a consistent max-product
//! heuristic `h` finalizes a fine product state `s = (X, q)` iff
//! `inside(s) · h(s) ≥ P*`, where `P*` is the best goal score. `inside(s)` and
//! `P*` are heuristic-independent, so a single exhaustive fine parse lets us tally
//! `predicted_finalized(h) = #{ reachable s : inside(s) · h(s) ≥ P* }` for any `h`.
//!
//! For each sentence this probe:
//!   1. builds the exhaustive fine chart (`materialize_indexed_..._with_pairs`),
//!   2. computes Viterbi inside weights and `P*` in log-prob space,
//!   3. evaluates `h ∈ {zero, SX, F, min(SX,F)}` per product state,
//!   4. tallies `predicted_finalized` for each.
//!
//! Everything is in log-prob space to match the `LogProbabilityScorer` A* path
//! (so `SX` self-validates against the `astar-sx` `finalized_states`), and to
//! avoid underflow on long sentences. In that space the merit test is
//! `inside(s) + h(s) ≥ P*`, F contributes `0` (pass) or `-inf` (prune), and
//! `min(SX, F)` is the numeric min.
//!
//! Usage: f-step2-probe <GRAMMAR.irtg> <SENTENCES.txt>

use rusty_alto::combinators::InvHom;
use rusty_alto::homomorphism::HomLabel;
use rusty_alto::materialize::materialize_indexed_condensed_intersection_with_pairs;
use rusty_alto::{
    parse_irtg, Explicit, IntersectionHeuristic, LogProbabilityScorer,
    SentenceSxHeuristic, Span, StateId, StringAlgebra, StringDecompositionAutomaton, Symbol,
    TopDownTa, UniversalSxHeuristic,
};
use packed_term_arena::tree::Tree;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{BufRead, BufReader};

/// Sparse leaf multiset: leaf-symbol id -> count (absent key == 0).
type Bag = BTreeMap<u32, u32>;
type ObligationTables = (Vec<Option<Bag>>, Vec<Option<Bag>>, Vec<Option<Bag>>);

// ---------------------------------------------------------------------------
// Obligatory-leaf tables (Statistic A — same logic as the Step 1 probe)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Tok {
    Word(u32),
    Child(usize),
}

#[derive(Clone, Debug)]
struct FlatRule {
    result: usize,
    tokens: Vec<Tok>,
}

fn frontier(
    arena: &packed_term_arena::tree::TreeArena<HomLabel>,
    node: Tree,
    children: &[StateId],
    out: &mut Vec<Tok>,
) {
    match *arena.get_label(node) {
        HomLabel::Var(i) => {
            if let Some(c) = children.get(i) {
                out.push(Tok::Child(c.index()));
            }
        }
        HomLabel::Symbol(s) => {
            let kids = arena.get_children(node);
            if kids.is_empty() {
                out.push(Tok::Word(s.0));
            } else {
                for &k in kids {
                    frontier(arena, k, children, out);
                }
            }
        }
    }
}

fn extract_flat_rules(
    grammar: &Explicit,
    hom: &rusty_alto::homomorphism::Homomorphism,
    num_states: usize,
) -> (Vec<FlatRule>, Vec<usize>) {
    let arena = hom.arena();
    let mut flat_rules = Vec::new();
    for rule in grammar.rules() {
        let Some(term) = hom.get(rule.symbol) else {
            continue;
        };
        let children: &[StateId] = rule.children;
        if children
            .iter()
            .any(|c| c.is_stuck() || c.index() >= num_states)
            || rule.result.is_stuck()
            || rule.result.index() >= num_states
        {
            continue;
        }
        let mut tokens = Vec::new();
        frontier(arena, term, children, &mut tokens);
        flat_rules.push(FlatRule {
            result: rule.result.index(),
            tokens,
        });
    }
    let mut accepting = Vec::new();
    grammar.initial_states(&mut |s: StateId| {
        if !s.is_stuck() && s.index() < num_states {
            accepting.push(s.index());
        }
    });
    (flat_rules, accepting)
}

fn bag_add(acc: &mut Bag, other: &Bag) {
    for (&k, &v) in other {
        *acc.entry(k).or_insert(0) += v;
    }
}

/// Per-key min; drops keys whose min is 0 (= absent from one side).
fn bag_min(a: &Bag, b: &Bag) -> Bag {
    let mut out = Bag::new();
    for (&k, &av) in a {
        if let Some(&bv) = b.get(&k) {
            let m = av.min(bv);
            if m > 0 {
                out.insert(k, m);
            }
        }
    }
    out
}

fn meet_update(slot: &mut Option<Bag>, cand: Bag, changed: &mut bool) {
    let new = match slot.as_ref() {
        None => cand,
        Some(cur) => bag_min(cur, &cand),
    };
    if slot.as_ref() != Some(&new) {
        *slot = Some(new);
        *changed = true;
    }
}

/// Returns `(mic, req_left, req_right)`, each `Vec<Option<Bag>>` of length
/// `num_states`. `None` = non-productive / unreachable (never an A* item).
fn compute_obligatory(
    num_states: usize,
    flat_rules: &[FlatRule],
    accepting: &[usize],
) -> ObligationTables {
    // mic: obligatory INSIDE leaves. MEET (per-key min) over a state's rules.
    let mut mic: Vec<Option<Bag>> = vec![None; num_states];
    loop {
        let mut changed = false;
        for r in flat_rules {
            let mut acc = Bag::new();
            let mut feasible = true;
            for tok in &r.tokens {
                match tok {
                    Tok::Word(s) => {
                        *acc.entry(*s).or_insert(0) += 1;
                    }
                    Tok::Child(c) => match &mic[*c] {
                        Some(m) => bag_add(&mut acc, m),
                        None => {
                            feasible = false;
                            break;
                        }
                    },
                }
            }
            if !feasible {
                continue;
            }
            meet_update(&mut mic[r.result], acc, &mut changed);
        }
        if !changed {
            break;
        }
    }

    // Only rules whose every child is productive can appear in a finite parse.
    let productive_rules: Vec<&FlatRule> = flat_rules
        .iter()
        .filter(|r| {
            r.tokens.iter().all(|t| match t {
                Tok::Child(c) => mic[*c].is_some(),
                _ => true,
            })
        })
        .collect();

    // req_left / req_right: obligatory OUTSIDE leaves. Roots seed to ∅.
    let mut req_left: Vec<Option<Bag>> = vec![None; num_states];
    let mut req_right: Vec<Option<Bag>> = vec![None; num_states];
    for &a in accepting {
        req_left[a] = Some(Bag::new());
        req_right[a] = Some(Bag::new());
    }

    loop {
        let mut changed = false;
        for r in &productive_rules {
            for (pos, tok) in r.tokens.iter().enumerate() {
                let x = match tok {
                    Tok::Child(c) => *c,
                    _ => continue,
                };
                // Within-rule obligations strictly left / right of THIS position.
                let mut left = Bag::new();
                let mut right = Bag::new();
                for (q, t2) in r.tokens.iter().enumerate() {
                    if q == pos {
                        continue;
                    }
                    let side = if q < pos { &mut left } else { &mut right };
                    match t2 {
                        Tok::Word(s) => {
                            *side.entry(*s).or_insert(0) += 1;
                        }
                        // Productive ⇒ mic is Some.
                        Tok::Child(c) => bag_add(side, mic[*c].as_ref().unwrap()),
                    }
                }
                if let Some(pr) = req_right[r.result].clone() {
                    let mut cand = pr;
                    bag_add(&mut cand, &right);
                    meet_update(&mut req_right[x], cand, &mut changed);
                }
                if let Some(pl) = req_left[r.result].clone() {
                    let mut cand = pl;
                    bag_add(&mut cand, &left);
                    meet_update(&mut req_left[x], cand, &mut changed);
                }
            }
        }
        if !changed {
            break;
        }
    }

    (mic, req_left, req_right)
}

// ---------------------------------------------------------------------------
// Inside weights (Viterbi / max-product), log-prob space
// ---------------------------------------------------------------------------

/// `inside[s]` = best (max-product) log-weight of any derivation rooted at
/// product state `s`. `-inf` for states with no finite derivation.
fn compute_inside_log(chart: &Explicit, num_products: usize) -> Vec<f64> {
    let mut inside = vec![f64::NEG_INFINITY; num_products];
    loop {
        let mut changed = false;
        for rule in chart.rules() {
            let mut cand = if rule.weight == 0.0 {
                f64::NEG_INFINITY
            } else {
                rule.weight.ln()
            };
            for &c in rule.children {
                let ci = inside[c.index()];
                if ci == f64::NEG_INFINITY {
                    cand = f64::NEG_INFINITY;
                    break;
                }
                cand += ci;
            }
            let slot = &mut inside[rule.result.index()];
            if cand > *slot {
                *slot = cand;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    inside
}

// ---------------------------------------------------------------------------
// F heuristic (obligatory-leaf suffix filter), log-prob space
// ---------------------------------------------------------------------------

/// Can the sentence slice `syms` supply every required (leaf, count) in `req`?
fn supply_covers(req: &Bag, syms: &[u32]) -> bool {
    for (&sym, &need) in req {
        let have = syms.iter().filter(|&&s| s == sym).count();
        if have < need as usize {
            return false;
        }
    }
    true
}

/// F estimate in log space: `0.0` (pass, no outside info) or `-inf` (prune:
/// an obligatory leaf is missing from the context the span leaves available).
fn f_estimate_log(
    left: StateId,
    span: &Span,
    sentence: &[u32],
    req_left: &[Option<Bag>],
    req_right: &[Option<Bag>],
) -> f64 {
    let idx = left.index();
    let n = sentence.len();
    let left_supply = &sentence[..span.start.min(n)];
    let right_supply = &sentence[span.end.min(n)..];

    if let Some(Some(req)) = req_left.get(idx).map(|o| o.as_ref())
        && !supply_covers(req, left_supply)
    {
        return f64::NEG_INFINITY;
    }
    if let Some(Some(req)) = req_right.get(idx).map(|o| o.as_ref())
        && !supply_covers(req, right_supply)
    {
        return f64::NEG_INFINITY;
    }
    0.0
}

/// Load a `UniversalSxHeuristic` from `<grammar>.sxcache/nmax<N>.bin` (exact N,
/// else the smallest cached `n_max >= n_needed`) — the same cache `ptb-eval`
/// writes. Returns `None` if nothing usable is found.
fn load_sx_cache(grammar_path: &str, n_needed: usize) -> Option<UniversalSxHeuristic> {
    use std::path::PathBuf;
    let dir = PathBuf::from(format!("{grammar_path}.sxcache"));

    let try_load = |p: &std::path::Path| -> Option<UniversalSxHeuristic> {
        let bytes = std::fs::read(p).ok()?;
        UniversalSxHeuristic::from_bytes(&bytes).filter(|h| h.n_max() >= n_needed)
    };

    if let Some(h) = try_load(&dir.join(format!("nmax{n_needed}.bin"))) {
        return Some(h);
    }
    // Fall back to the smallest cached table that still covers n_needed.
    let mut candidates: Vec<(usize, PathBuf)> = std::fs::read_dir(&dir)
        .ok()?
        .flatten()
        .filter_map(|e| {
            let p = e.path();
            let stem = p.file_stem()?.to_str()?.strip_prefix("nmax")?.parse().ok()?;
            (stem >= n_needed).then_some((stem, p))
        })
        .collect();
    candidates.sort_by_key(|(n, _)| *n);
    candidates.into_iter().find_map(|(_, p)| try_load(&p))
}

// ---------------------------------------------------------------------------
// Main probe
// ---------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: f-step2-probe <GRAMMAR.irtg> <SENTENCES.txt>");
        std::process::exit(1);
    }
    let grammar_path = &args[1];
    let sentences_path = &args[2];

    let irtg = parse_irtg(BufReader::new(File::open(grammar_path)?))?;
    let grammar = irtg.grammar();
    let num_states = grammar.num_states() as usize;
    let name = irtg
        .string_interpretation_names()
        .first()
        .copied()
        .ok_or("no string interpretation found")?
        .to_string();
    let interp = irtg.interpretation::<StringAlgebra>(&name)?;
    let hom = interp.homomorphism();
    let concat = interp
        .algebra_signature()
        .get("*")
        .unwrap_or(rusty_alto::Symbol(0));

    eprintln!("Grammar: {num_states} states  (interpretation \"{name}\")");

    // Obligatory-leaf tables (once per grammar).
    let (flat_rules, accepting) = extract_flat_rules(grammar, hom, num_states);
    let (_mic, req_left, req_right) = compute_obligatory(num_states, &flat_rules, &accepting);
    eprintln!("Flat rules: {}  accepting: {}", flat_rules.len(), accepting.len());

    // Load sentences via the algebra parser (handles interning).
    let mut sentences: Vec<Vec<Symbol>> = Vec::new();
    for line in BufReader::new(File::open(sentences_path)?).lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        sentences.push(interp.parse_object(&line)?);
    }
    let n_max = sentences.iter().map(|s| s.len()).max().unwrap_or(0);
    eprintln!("Sentences: {}  (max length {n_max})", sentences.len());

    // Reuse the SX cache next to the grammar (`<grammar>.sxcache/nmax<N>.bin`,
    // the same layout `ptb-eval` writes); the n_max=41 build is multi-minute and
    // ~3.5 GB, so loading the 1.1 GB cache is the only sane path here.
    let sx_table = match load_sx_cache(grammar_path, n_max) {
        Some(h) => {
            eprintln!("Loaded SX cache (n_max={})", h.n_max());
            h
        }
        None => {
            eprintln!("Building SX heuristic (n_max={n_max})... (no usable cache found)");
            UniversalSxHeuristic::new_with(grammar, hom, concat, n_max, &LogProbabilityScorer)
        }
    };

    println!("sentence_no,n,reachable,zero_fin,sx_fin,f_fin,min_fin");

    let mut tot_reach = 0usize;
    let mut tot_zero = 0usize;
    let mut tot_sx = 0usize;
    let mut tot_f = 0usize;
    let mut tot_min = 0usize;
    let mut no_parse = 0usize;

    for (si, sentence) in sentences.iter().enumerate() {
        let n = sentence.len();
        let sent_syms: Vec<u32> = sentence.iter().map(|s| s.0).collect();

        // Exhaustive fine chart + product-state -> (grammar state, right state) map.
        let decomp = StringDecompositionAutomaton::new(concat, sentence.clone());
        let invhom = InvHom::new(decomp, hom);
        let (chart, right_interner, pairs, _stats) =
            materialize_indexed_condensed_intersection_with_pairs(grammar, &invhom);

        let num_products = pairs.len();
        let inside = compute_inside_log(&chart, num_products);

        // P* = best inside over accepting (goal) product states.
        let mut p_star = f64::NEG_INFINITY;
        chart.initial_states(&mut |s: StateId| {
            let v = inside[s.index()];
            if v > p_star {
                p_star = v;
            }
        });

        if p_star == f64::NEG_INFINITY {
            no_parse += 1;
            println!("{},{},{},,,,", si + 1, n, num_products);
            continue;
        }

        let sx_h = sx_table.for_sentence(n);

        let mut reach = 0usize;
        let (mut zero_c, mut sx_c, mut f_c, mut min_c) = (0usize, 0usize, 0usize, 0usize);
        for (i, &(left_state, right_id)) in pairs.iter().enumerate() {
            let inside_s = inside[i];
            if inside_s == f64::NEG_INFINITY {
                continue; // not a reachable item in a finite parse
            }
            reach += 1;
            let span: &Span = right_interner.resolve(right_id);

            // h in log space; merit = inside + h; finalize iff merit >= P*.
            let h_sx = <SentenceSxHeuristic<'_> as IntersectionHeuristic<
                StringDecompositionAutomaton,
            >>::outside_estimate(&sx_h, left_state, span);
            let h_f = f_estimate_log(left_state, span, &sent_syms, &req_left, &req_right);
            let h_min = h_sx.min(h_f);

            zero_c += (inside_s >= p_star) as usize; // h_zero = 0
            sx_c += (inside_s + h_sx >= p_star) as usize;
            f_c += (inside_s + h_f >= p_star) as usize;
            min_c += (inside_s + h_min >= p_star) as usize;
        }

        tot_reach += reach;
        tot_zero += zero_c;
        tot_sx += sx_c;
        tot_f += f_c;
        tot_min += min_c;
        println!("{},{},{},{},{},{},{}", si + 1, n, reach, zero_c, sx_c, f_c, min_c);
    }

    let pct = |part: usize, whole: usize| {
        if whole == 0 {
            0.0
        } else {
            part as f64 / whole as f64
        }
    };
    eprintln!();
    eprintln!("=== SUMMARY (predicted_finalized over reachable items) ===");
    eprintln!("sentences parsed : {}  (no-parse: {no_parse})", sentences.len() - no_parse);
    eprintln!("reachable items  : {tot_reach}");
    eprintln!("zero  finalized  : {tot_zero}  ({:.3})", pct(tot_zero, tot_reach));
    eprintln!("SX    finalized  : {tot_sx}  ({:.3})", pct(tot_sx, tot_reach));
    eprintln!("F     finalized  : {tot_f}  ({:.3})", pct(tot_f, tot_reach));
    eprintln!("min   finalized  : {tot_min}  ({:.3})", pct(tot_min, tot_reach));
    eprintln!();
    eprintln!("SX  saves vs zero : {:.1}%", (1.0 - pct(tot_sx, tot_zero)) * 100.0);
    eprintln!("min saves vs zero : {:.1}%", (1.0 - pct(tot_min, tot_zero)) * 100.0);
    eprintln!("min saves vs SX   : {:.1}%", (1.0 - pct(tot_min, tot_sx)) * 100.0);
    println!(
        "SUMMARY reach={tot_reach} zero={tot_zero} sx={tot_sx} f={tot_f} min={tot_min} \
         min_vs_sx={:.4}",
        1.0 - pct(tot_min, tot_sx)
    );

    Ok(())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Grammar: S=0, A=1, B=2 ; words x=10, y=11, z=12.
    //   r1: S -> A B    r2: A -> "x"    r3: B -> "y"    r4: A -> "z"
    fn sample() -> (usize, Vec<FlatRule>, Vec<usize>) {
        let rules = vec![
            FlatRule { result: 0, tokens: vec![Tok::Child(1), Tok::Child(2)] },
            FlatRule { result: 1, tokens: vec![Tok::Word(10)] },
            FlatRule { result: 2, tokens: vec![Tok::Word(11)] },
            FlatRule { result: 1, tokens: vec![Tok::Word(12)] },
        ];
        (3, rules, vec![0])
    }

    fn bag(pairs: &[(u32, u32)]) -> Bag {
        pairs.iter().copied().collect()
    }

    #[test]
    fn obligatory_fixpoints_match_worked_example() {
        let (n, rules, accepting) = sample();
        let (mic, req_left, req_right) = compute_obligatory(n, &rules, &accepting);

        // mic[A] = {} (x OR z), mic[B] = {y}, mic[S] = {y}.
        assert_eq!(mic[1], Some(bag(&[])));
        assert_eq!(mic[2], Some(bag(&[(11, 1)])));
        assert_eq!(mic[0], Some(bag(&[(11, 1)])));

        // A always has a y to its right; nothing to its left.
        assert_eq!(req_right[1], Some(bag(&[(11, 1)])));
        assert_eq!(req_left[1], Some(bag(&[])));
        // A forces nothing, so B's sides are empty.
        assert_eq!(req_left[2], Some(bag(&[])));
        assert_eq!(req_right[2], Some(bag(&[])));
        // Root has empty obligations.
        assert_eq!(req_left[0], Some(bag(&[])));
        assert_eq!(req_right[0], Some(bag(&[])));
    }

    #[test]
    fn f_prunes_when_required_leaf_missing_on_side() {
        let (n, rules, accepting) = sample();
        let (_mic, req_left, req_right) = compute_obligatory(n, &rules, &accepting);
        let a = StateId(1);

        // A needs a y to its right. Sentence "x y": A spans [0,1), right supply = [y] -> pass.
        let pass = f_estimate_log(a, &Span::new(0, 1), &[10, 11], &req_left, &req_right);
        assert_eq!(pass, 0.0);

        // A spanning [0,2) of "x y" leaves no right supply -> the required y is gone -> prune.
        let prune = f_estimate_log(a, &Span::new(0, 2), &[10, 11], &req_left, &req_right);
        assert_eq!(prune, f64::NEG_INFINITY);
    }

    #[test]
    fn min_is_numeric_min_in_log_space() {
        // min(SX, F): F=-inf dominates; else SX passes through.
        assert_eq!((-0.5f64).min(f64::NEG_INFINITY), f64::NEG_INFINITY);
        assert_eq!((-0.5f64).min(0.0), -0.5);
    }
}
