use crate::{FxHashMap, Symbol};
use std::fmt;

/// Bidirectional map between external label names and dense [`Symbol`] IDs.
///
/// Runners never look at strings: they expect tree arenas to store raw
/// [`Symbol`] values. A signature is the loading-time bridge that keeps an
/// automaton and its trees in the same symbol space. Intern labels while
/// reading the automaton, then use the same signature to compile input trees.
#[derive(Clone, Debug, Default)]
pub struct Signature {
    names: Vec<String>,
    ids: FxHashMap<String, Symbol>,
    arities: FxHashMap<Symbol, usize>,
}

impl Signature {
    /// Create an empty signature.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the symbol ID for a name, inserting it if needed.
    ///
    /// If the name was already interned with a different arity, the signature
    /// is left unchanged and [`SignatureError::ArityMismatch`] is returned.
    pub fn intern(&mut self, name: String, arity: usize) -> Result<Symbol, SignatureError> {
        if let Some(&symbol) = self.ids.get(&name) {
            let old_arity = self.arities[&symbol];
            if old_arity != arity {
                return Err(SignatureError::ArityMismatch {
                    symbol: name,
                    first: old_arity,
                    second: arity,
                });
            }
            return Ok(symbol);
        }

        let id = u32::try_from(self.names.len()).expect("too many symbols for Symbol");
        let symbol = Symbol(id);
        self.names.push(name.clone());
        self.ids.insert(name, symbol);
        self.arities.insert(symbol, arity);
        Ok(symbol)
    }

    /// Look up a symbol ID by name without inserting it.
    pub fn get(&self, name: &str) -> Option<Symbol> {
        self.ids.get(name).copied()
    }

    /// Resolve a symbol ID back to its external label.
    ///
    /// Panics if `symbol` is not present in this signature.
    pub fn resolve(&self, symbol: Symbol) -> &str {
        &self.names[symbol.0 as usize]
    }

    /// Return the arity recorded for a symbol.
    ///
    /// Panics if `symbol` is not present in this signature.
    pub fn arity(&self, symbol: Symbol) -> usize {
        self.arities[&symbol]
    }

    /// Return the number of labels in the signature.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Return whether the signature contains no labels.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

/// Error returned when a label cannot be interned into a [`Signature`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignatureError {
    /// The same label was observed with two different arities.
    ArityMismatch {
        /// Label name.
        symbol: String,
        /// First recorded arity.
        first: usize,
        /// Later conflicting arity.
        second: usize,
    },
}

impl fmt::Display for SignatureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArityMismatch {
                symbol,
                first,
                second,
            } => write!(
                f,
                "symbol {symbol:?} used with arities {first} and {second}"
            ),
        }
    }
}

impl std::error::Error for SignatureError {}

impl fmt::Display for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, name) in self.names.iter().enumerate() {
            if idx > 0 {
                writeln!(f)?;
            }
            let symbol = Symbol(idx as u32);
            write!(f, "{} / {}", name, self.arity(symbol))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_labels_stably() {
        let mut sig = Signature::new();
        let a = sig.intern("a".to_owned(), 0).unwrap();
        let f = sig.intern("f".to_owned(), 2).unwrap();
        assert_eq!(sig.intern("a".to_owned(), 0), Ok(a));
        assert_ne!(a, f);
        assert_eq!(sig.get("f"), Some(f));
        assert_eq!(sig.resolve(a), "a");
        assert_eq!(sig.arity(f), 2);
    }

    #[test]
    fn rejects_arity_mismatches() {
        let mut sig = Signature::new();
        sig.intern("f".to_owned(), 1).unwrap();
        assert!(matches!(
            sig.intern("f".to_owned(), 2),
            Err(SignatureError::ArityMismatch { .. })
        ));
    }
}
