//! Obligatory-leaf coverage probe (Step 1 of the F-heuristic plan).
//!
//! Usage: oblig-coverage <GRAMMAR.irtg> [--examples N]
//!
//! Reads an IRTG grammar (same file passed to ptb-eval), extracts the first
//! string interpretation, and computes three per-state tables:
//!   mic[X]       – multiset of leaves every derivation of X must contain
//!   req_left[X]  – leaves every *completion* of X emits strictly to X's left
//!   req_right[X] – leaves every *completion* of X emits strictly to X's right
//!
//! Then reports coverage statistics so we can judge whether an F-style
//! obligatory-leaf filter would prune any A* items.

use rusty_alto::homomorphism::HomLabel;
use rusty_alto::{parse_irtg, StateId, StringAlgebra, Symbol, TopDownTa};
use rusty_tree::tree::Tree;
use std::collections::BTreeMap;
use std::env;
use std::fs::File;
use std::io::BufReader;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// One flattened left-to-right yield token.
#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Word(u32),   // leaf symbol id
    Child(usize), // child state index
}

/// A grammar rule reduced to what the analysis needs.
#[derive(Clone, Debug)]
struct FlatRule {
    result: usize,
    tokens: Vec<Tok>,
}

/// Sparse leaf multiset: symbol-id → count.
type Bag = BTreeMap<u32, u32>;

// ---------------------------------------------------------------------------
// Bag helpers
// ---------------------------------------------------------------------------

fn bag_add(a: &mut Bag, b: &Bag) {
    for (&sym, &cnt) in b {
        *a.entry(sym).or_insert(0) += cnt;
    }
}

/// Per-key min; keys absent from either bag are treated as 0 and dropped.
fn bag_min(a: &Bag, b: &Bag) -> Bag {
    let mut out = Bag::new();
    for (&sym, &ca) in a {
        if let Some(&cb) = b.get(&sym) {
            let m = ca.min(cb);
            if m > 0 {
                out.insert(sym, m);
            }
        }
        // absent from b → min is 0 → don't insert
    }
    out
}

// ---------------------------------------------------------------------------
// Phase A — flatten rules
// ---------------------------------------------------------------------------

fn frontier(
    arena: &rusty_tree::tree::TreeArena<HomLabel>,
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
    grammar: &rusty_alto::Explicit,
    hom: &rusty_alto::homomorphism::Homomorphism,
    num_states: usize,
) -> (Vec<FlatRule>, Vec<usize>) {
    let arena = hom.arena();
    let mut flat_rules = Vec::new();

    for rule in grammar.rules() {
        let Some(term) = hom.get(rule.symbol) else {
            continue;
        };
        // Skip rules with stuck or out-of-range children.
        let children: &[StateId] = rule.children;
        if children.iter().any(|c| c.is_stuck() || c.index() >= num_states) {
            continue;
        }
        if rule.result.is_stuck() || rule.result.index() >= num_states {
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

// ---------------------------------------------------------------------------
// Core computation (also used by tests)
// ---------------------------------------------------------------------------

fn compute(
    num_states: usize,
    flat_rules: &[FlatRule],
    accepting: &[usize],
) -> (Vec<Option<Bag>>, Vec<Option<Bag>>, Vec<Option<Bag>>) {
    // Phase B: mic
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
                        None => {
                            feasible = false;
                            break;
                        }
                        Some(m) => {
                            let m = m.clone();
                            bag_add(&mut acc, &m);
                        }
                    },
                }
            }
            if !feasible {
                continue;
            }
            let new = match &mic[r.result] {
                None => acc,
                Some(cur) => bag_min(cur, &acc),
            };
            if mic[r.result].as_ref() != Some(&new) {
                mic[r.result] = Some(new);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Phase C: req_left / req_right
    // Only use productive rules (every Child(c) has mic[c] = Some).
    let productive_rules: Vec<&FlatRule> = flat_rules
        .iter()
        .filter(|r| {
            r.tokens.iter().all(|t| match t {
                Tok::Child(c) => mic[*c].is_some(),
                _ => true,
            })
        })
        .collect();

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

                // Collect within-rule obligations to left and right of position pos.
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
                        Tok::Child(c) => {
                            // productive_rules guarantees mic[c] = Some
                            let m = mic[*c].as_ref().unwrap().clone();
                            bag_add(side, &m);
                        }
                    }
                }

                // Propagate parent's req_right + within-rule right to child's req_right.
                if let Some(pr) = req_right[r.result].clone() {
                    let mut cand = pr;
                    bag_add(&mut cand, &right);
                    meet_update(&mut req_right[x], cand, &mut changed);
                }

                // Propagate parent's req_left + within-rule left to child's req_left.
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

// ---------------------------------------------------------------------------
// Phase D — report
// ---------------------------------------------------------------------------

fn report(
    num_states: usize,
    mic: &[Option<Bag>],
    req_left: &[Option<Bag>],
    req_right: &[Option<Bag>],
    sig: &rusty_alto::Signature,
    examples: usize,
) {
    let productive: Vec<usize> = (0..num_states).filter(|&i| mic[i].is_some()).collect();
    let reachable: Vec<usize> = (0..num_states)
        .filter(|&i| req_left[i].is_some() || req_right[i].is_some())
        .collect();
    let universe: Vec<usize> = (0..num_states)
        .filter(|&i| mic[i].is_some() && (req_left[i].is_some() || req_right[i].is_some()))
        .collect();

    println!("=== Obligatory-leaf coverage report ===");
    println!("total states      : {}", num_states);
    println!("productive        : {}", productive.len());
    println!("root-reachable    : {}", reachable.len());
    println!("|U| (both)        : {}", universe.len());
    println!();

    if universe.is_empty() {
        println!("No item-eligible states — nothing to measure.");
        println!("SUMMARY productive=0 reachable=0 universe=0 frac_mic_nonempty=0.00 frac_req_nonempty=0.00");
        return;
    }

    let u = universe.len() as f64;

    let mic_nonempty: Vec<usize> = universe
        .iter()
        .copied()
        .filter(|&i| !mic[i].as_ref().unwrap().is_empty())
        .collect();
    let req_left_nonempty: Vec<usize> = universe
        .iter()
        .copied()
        .filter(|&i| req_left[i].as_ref().map_or(false, |b| !b.is_empty()))
        .collect();
    let req_right_nonempty: Vec<usize> = universe
        .iter()
        .copied()
        .filter(|&i| req_right[i].as_ref().map_or(false, |b| !b.is_empty()))
        .collect();
    let req_any_nonempty: Vec<usize> = universe
        .iter()
        .copied()
        .filter(|&i| {
            req_left[i].as_ref().map_or(false, |b| !b.is_empty())
                || req_right[i].as_ref().map_or(false, |b| !b.is_empty())
        })
        .collect();

    println!("Over |U|:");
    println!(
        "  mic non-empty       : {} / {} = {:.3}",
        mic_nonempty.len(),
        universe.len(),
        mic_nonempty.len() as f64 / u
    );
    println!(
        "  req_left non-empty  : {} / {} = {:.3}",
        req_left_nonempty.len(),
        universe.len(),
        req_left_nonempty.len() as f64 / u
    );
    println!(
        "  req_right non-empty : {} / {} = {:.3}",
        req_right_nonempty.len(),
        universe.len(),
        req_right_nonempty.len() as f64 / u
    );
    println!(
        "  req_any non-empty   : {} / {} = {:.3}  ← HEADLINE",
        req_any_nonempty.len(),
        universe.len(),
        req_any_nonempty.len() as f64 / u
    );
    println!();

    // Distribution of obligation size for states with any obligation.
    if !req_any_nonempty.is_empty() {
        let mut sizes_distinct: Vec<usize> = req_any_nonempty
            .iter()
            .map(|&i| {
                let rl = req_left[i].as_ref().map_or(0, |b| b.len());
                let rr = req_right[i].as_ref().map_or(0, |b| b.len());
                rl + rr
            })
            .collect();
        let mut sizes_total: Vec<u32> = req_any_nonempty
            .iter()
            .map(|&i| {
                let rl: u32 = req_left[i].as_ref().map_or(0, |b| b.values().sum());
                let rr: u32 = req_right[i].as_ref().map_or(0, |b| b.values().sum());
                rl + rr
            })
            .collect();
        sizes_distinct.sort_unstable();
        sizes_total.sort_unstable();

        let pct = |v: &[usize], p: f64| -> usize {
            let idx = ((v.len() as f64) * p) as usize;
            v[idx.min(v.len() - 1)]
        };
        let pct_u32 = |v: &[u32], p: f64| -> u32 {
            let idx = ((v.len() as f64) * p) as usize;
            v[idx.min(v.len() - 1)]
        };
        let mean_d = sizes_distinct.iter().sum::<usize>() as f64 / sizes_distinct.len() as f64;
        let mean_t = sizes_total.iter().sum::<u32>() as f64 / sizes_total.len() as f64;

        println!("Obligation size distribution (states with req_any non-empty: {}):", req_any_nonempty.len());
        println!(
            "  distinct terminals: min={} median={} mean={:.1} p90={} max={}",
            sizes_distinct.first().unwrap(),
            pct(&sizes_distinct, 0.5),
            mean_d,
            pct(&sizes_distinct, 0.9),
            sizes_distinct.last().unwrap()
        );
        println!(
            "  total count       : min={} median={} mean={:.1} p90={} max={}",
            sizes_total.first().unwrap(),
            pct_u32(&sizes_total, 0.5),
            mean_t,
            pct_u32(&sizes_total, 0.9),
            sizes_total.last().unwrap()
        );
        println!();

        // Top 15 terminals by number of states requiring them.
        let mut term_counts: BTreeMap<u32, usize> = BTreeMap::new();
        for &i in &req_any_nonempty {
            for bag in [req_left[i].as_ref(), req_right[i].as_ref()]
                .into_iter()
                .flatten()
            {
                for &sym in bag.keys() {
                    *term_counts.entry(sym).or_insert(0) += 1;
                }
            }
        }
        let mut ranked: Vec<(usize, u32)> = term_counts.into_iter().map(|(k, v)| (v, k)).collect();
        ranked.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        println!("Top 15 obligatory terminals (by # states requiring them):");
        for (count, sym) in ranked.iter().take(15) {
            let word = sig.resolve(Symbol(*sym));
            println!("  {:>6} states  {:?}", count, word);
        }
        println!();

        // Examples.
        println!("Example states with obligations (up to {examples}):");
        for &i in req_any_nonempty.iter().take(examples) {
            let rl: Vec<String> = req_left[i]
                .as_ref()
                .map(|b| {
                    b.iter()
                        .map(|(&s, &c)| format!("{}:{}", sig.resolve(Symbol(s)), c))
                        .collect()
                })
                .unwrap_or_default();
            let rr: Vec<String> = req_right[i]
                .as_ref()
                .map(|b| {
                    b.iter()
                        .map(|(&s, &c)| format!("{}:{}", sig.resolve(Symbol(s)), c))
                        .collect()
                })
                .unwrap_or_default();
            println!(
                "  state {}: req_left=[{}]  req_right=[{}]",
                i,
                rl.join(", "),
                rr.join(", ")
            );
        }
        println!();
    }

    // Verdict.
    let frac = req_any_nonempty.len() as f64 / u;
    let verdict = if frac >= 0.30 {
        "PROCEED to Step 2 (strong coverage)"
    } else if frac <= 0.05 {
        "STOP — coverage too low for F to help"
    } else {
        "INCONCLUSIVE — proceed to Step 2 to measure real pruning"
    };
    println!("Verdict: {verdict}");
    println!();

    println!(
        "SUMMARY productive={} reachable={} universe={} frac_mic_nonempty={:.3} frac_req_nonempty={:.3}",
        productive.len(),
        reachable.len(),
        universe.len(),
        mic_nonempty.len() as f64 / u,
        frac
    );
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: oblig-coverage <GRAMMAR.irtg> [--examples N]");
        std::process::exit(1);
    }
    let grammar_path = &args[1];
    let mut examples = 10usize;
    let mut i = 2;
    while i < args.len() {
        if args[i] == "--examples" {
            i += 1;
            if i < args.len() {
                examples = args[i].parse().unwrap_or(10);
            }
        }
        i += 1;
    }

    let file = File::open(grammar_path)?;
    let irtg = parse_irtg(BufReader::new(file))?;
    let grammar = irtg.grammar();
    let num_states = grammar.num_states() as usize;

    let names = irtg.string_interpretation_names();
    let name = names.first().ok_or("no string interpretation found")?;
    let interp = irtg.interpretation::<StringAlgebra>(name)?;
    let hom = interp.homomorphism();
    let sig = interp.algebra_signature();

    eprintln!("Grammar: {} states", num_states);
    eprintln!("Using interpretation: {name:?}");

    let (flat_rules, accepting) = extract_flat_rules(grammar, hom, num_states);
    eprintln!("Flat rules: {}  accepting: {}", flat_rules.len(), accepting.len());

    let (mic, req_left, req_right) = compute(num_states, &flat_rules, &accepting);

    report(num_states, &mic, &req_left, &req_right, sig, examples);

    Ok(())
}

// ---------------------------------------------------------------------------
// Unit test (correctness gate)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Hand-built grammar from the plan's worked example:
    ///   S=0, A=1, B=2;  word symbols x=10, y=11, z=12
    ///   r1: S -> A B        tokens=[Child(1), Child(2)]
    ///   r2: A -> "x"        tokens=[Word(10)]
    ///   r3: B -> "y"        tokens=[Word(11)]
    ///   r4: A -> "z"        tokens=[Word(12)]
    ///   accepting = [0]  (S is the root)
    ///
    /// Expected:
    ///   mic[A=1] = {}        (A derives "x" OR "z" — nothing forced)
    ///   mic[B=2] = {11:1}    (B always yields "y")
    ///   mic[S=0] = {11:1}    (every S contains a "y" from B)
    ///   req_right[A=1] = {11:1}  (A always has a B="y" to its right)
    ///   req_left[A=1]  = {}
    ///   req_left[B=2]  = {}      (A forces nothing, so B's left is empty)
    ///   req_right[B=2] = {}
    ///   req_left[S=0]  = {}
    ///   req_right[S=0] = {}
    #[test]
    fn worked_example() {
        let flat_rules = vec![
            FlatRule { result: 0, tokens: vec![Tok::Child(1), Tok::Child(2)] }, // S->A B
            FlatRule { result: 1, tokens: vec![Tok::Word(10)] },                // A->"x"
            FlatRule { result: 2, tokens: vec![Tok::Word(11)] },                // B->"y"
            FlatRule { result: 1, tokens: vec![Tok::Word(12)] },                // A->"z"
        ];
        let accepting = vec![0usize];

        let (mic, req_left, req_right) = compute(3, &flat_rules, &accepting);

        // mic[A=1] = {} (nothing forced: "x" or "z")
        assert_eq!(mic[1], Some(BTreeMap::new()), "mic[A] should be empty");

        // mic[B=2] = {11:1}
        let mut expected_mic_b = BTreeMap::new();
        expected_mic_b.insert(11u32, 1u32);
        assert_eq!(mic[2], Some(expected_mic_b.clone()), "mic[B] should be {{y:1}}");

        // mic[S=0] = {11:1}
        assert_eq!(mic[0], Some(expected_mic_b), "mic[S] should be {{y:1}}");

        // req_right[A=1] = {11:1}
        let mut expected_rr_a = BTreeMap::new();
        expected_rr_a.insert(11u32, 1u32);
        assert_eq!(req_right[1], Some(expected_rr_a), "req_right[A] should be {{y:1}}");

        // req_left[A=1] = {}
        assert_eq!(req_left[1], Some(BTreeMap::new()), "req_left[A] should be empty");

        // req_left[B=2] = {}  req_right[B=2] = {}
        assert_eq!(req_left[2], Some(BTreeMap::new()), "req_left[B] should be empty");
        assert_eq!(req_right[2], Some(BTreeMap::new()), "req_right[B] should be empty");

        // req_left[S=0] = {}  req_right[S=0] = {}
        assert_eq!(req_left[0], Some(BTreeMap::new()), "req_left[S] should be empty");
        assert_eq!(req_right[0], Some(BTreeMap::new()), "req_right[S] should be empty");
    }
}
