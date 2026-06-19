//! Rule-weight scoring conventions for Viterbi and A* algorithms.

/// Maps raw rule weights to the score algebra used by one-best algorithms.
///
/// `Explicit` stores the raw weights it was built with. Algorithms that combine
/// many weights use a scorer to decide how to interpret those raw values.
pub trait WeightScorer {
    /// Score for an impossible derivation.
    fn zero(&self) -> f64;

    /// Score for an empty product.
    fn one(&self) -> f64;

    /// Convert one raw rule weight into this scorer's representation.
    fn rule_score(&self, weight: f64) -> f64;

    /// Combine two scores along one derivation.
    fn times(&self, left: f64, right: f64) -> f64;

    /// Convert a final score back to a conventional raw weight.
    fn score_to_weight(&self, score: f64) -> f64;

    /// Return whether `candidate` is strictly better than `current`.
    #[inline]
    fn better(&self, candidate: f64, current: f64) -> bool {
        candidate > current
    }
}

/// Interpret raw weights as ordinary multiplicative weights.
#[derive(Clone, Copy, Debug, Default)]
pub struct ProbabilityScorer;

impl WeightScorer for ProbabilityScorer {
    #[inline]
    fn zero(&self) -> f64 {
        0.0
    }

    #[inline]
    fn one(&self) -> f64 {
        1.0
    }

    #[inline]
    fn rule_score(&self, weight: f64) -> f64 {
        weight
    }

    #[inline]
    fn times(&self, left: f64, right: f64) -> f64 {
        left * right
    }

    #[inline]
    fn score_to_weight(&self, score: f64) -> f64 {
        score
    }
}

/// Interpret raw weights as probabilities and combine them in log space.
#[derive(Clone, Copy, Debug, Default)]
pub struct LogProbabilityScorer;

impl WeightScorer for LogProbabilityScorer {
    #[inline]
    fn zero(&self) -> f64 {
        f64::NEG_INFINITY
    }

    #[inline]
    fn one(&self) -> f64 {
        0.0
    }

    #[inline]
    fn rule_score(&self, weight: f64) -> f64 {
        if weight == 0.0 {
            f64::NEG_INFINITY
        } else {
            weight.ln()
        }
    }

    #[inline]
    fn times(&self, left: f64, right: f64) -> f64 {
        left + right
    }

    #[inline]
    fn score_to_weight(&self, score: f64) -> f64 {
        score.exp()
    }
}
