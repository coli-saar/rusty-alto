//! Reading and writing Alto corpora.
//!
//! An Alto corpus is a text file describing a sequence of instances. A header declares the
//! comment prefix, whether the corpus is *annotated* (carries a derivation tree per instance),
//! and the interpretations (name + algebra class). Each instance is one line per interpretation
//! in declared order, optionally followed by a derivation-tree line, separated by blank lines.
//!
//! See <https://github.com/coli-saar/alto/wiki/Corpora>. This is a port of Alto's
//! `corpus::{Corpus, CorpusWriter, Instance}`, generic over [`Read`]/[`Write`].

use crate::{Irtg, Symbol};
use packed_term_arena::parser::parse_tree;
use packed_term_arena::tree::{Tree, TreeArena};
use std::any::Any;
use std::io::{self, BufRead, BufReader, Read, Write};
use thiserror::Error;

/// Placeholder written for an instance with no parse / null value (Alto convention).
const NULL_MARKER: &str = "_null_";

/// One parsed object of an instance: an interpretation name, its raw text line, and the
/// type-erased parsed value (taken when the instance is fed to the parser).
pub struct InterpObject {
    /// Interpretation name.
    pub name: String,
    /// The raw line as it appeared in the corpus.
    pub text: String,
    /// The parsed algebra value, or `None` once it has been consumed for parsing.
    pub value: Option<Box<dyn Any + Send>>,
}

/// A single corpus instance.
pub struct Instance {
    /// Parsed objects, one per interpretation, in declared order.
    pub objects: Vec<InterpObject>,
    /// The gold derivation tree (annotated corpora only); read for round-trip, not used by parsing.
    pub gold_derivation: Option<(TreeArena<String>, Tree)>,
}

impl Instance {
    /// Return the raw text of the interpretation named `name`, if present.
    pub fn text(&self, name: &str) -> Option<&str> {
        self.objects
            .iter()
            .find(|o| o.name == name)
            .map(|o| o.text.as_str())
    }
}

/// A corpus read from a [`Read`]: header metadata plus its instances.
pub struct Corpus {
    /// Whether the corpus carries a derivation tree per instance.
    pub annotated: bool,
    /// The comment marker found in the header (e.g. `"#"` or `"///"`).
    pub comment_prefix: String,
    /// Interpretation names in declared order.
    pub interpretation_order: Vec<String>,
    /// The parsed instances (at most `limit`, if one was given).
    pub instances: Vec<Instance>,
}

/// Errors returned while reading a corpus.
#[derive(Debug, Error)]
pub enum CorpusError {
    /// An I/O error occurred.
    #[error("io error: {0}")]
    Io(#[from] io::Error),
    /// The header line did not match `<prefix>IRTG (un)annotated corpus file, v1.0`.
    #[error("invalid corpus header (expected '<prefix>IRTG [un]annotated corpus file, v1.0')")]
    BadHeader,
    /// The header declared an unsupported corpus version.
    #[error("unsupported corpus version (expected v1.0)")]
    BadVersion,
    /// An instance did not have the expected number of lines.
    #[error("line {line}: malformed instance (expected {expected} lines, found {found})")]
    MalformedInstance {
        /// 1-based line number where the instance starts.
        line: usize,
        /// Number of lines expected for an instance.
        expected: usize,
        /// Number of non-blank lines found.
        found: usize,
    },
    /// An interpretation line could not be parsed by its algebra.
    #[error("line {line}: cannot parse object for interpretation {interpretation:?}: {message}")]
    ObjectParse {
        /// 1-based line number.
        line: usize,
        /// Interpretation name.
        interpretation: String,
        /// Underlying parse error.
        message: String,
    },
    /// A derivation-tree line could not be parsed.
    #[error("line {line}: cannot parse derivation tree: {message}")]
    TreeParse {
        /// 1-based line number.
        line: usize,
        /// Underlying parse error.
        message: String,
    },
}

/// Read an Alto corpus, parsing every interpretation line with its algebra's `parse_object`.
///
/// `irtg` supplies the interpretations and their algebras. If `limit` is `Some(n)`, only the
/// first `n` instances are parsed. **Panics** if the corpus declares an interpretation the IRTG
/// does not contain.
pub fn read_corpus<R: Read>(
    reader: R,
    irtg: &Irtg,
    limit: Option<usize>,
) -> Result<Corpus, CorpusError> {
    let all: Vec<String> = BufReader::new(reader)
        .lines()
        .collect::<io::Result<_>>()?;

    let mut i = 0usize;

    // --- header --------------------------------------------------------------------------
    while i < all.len() && all[i].trim().is_empty() {
        i += 1;
    }
    let header = all.get(i).ok_or(CorpusError::BadHeader)?;
    let pos = header.find("IRTG").ok_or(CorpusError::BadHeader)?;
    let marker = header[..pos].trim_end().to_string();
    let rest = &header[pos..];
    if !rest.contains("1.0") {
        return Err(CorpusError::BadVersion);
    }
    let annotated = if rest.contains("unannotated") {
        false
    } else if rest.contains("annotated") {
        true
    } else {
        return Err(CorpusError::BadHeader);
    };
    i += 1;

    let mut interpretation_order = Vec::new();
    while i < all.len() {
        let line = &all[i];
        if line.trim().is_empty() {
            i += 1;
            break; // a blank line ends the header
        }
        if !marker.is_empty() && line.starts_with(&marker) {
            let content = line[marker.len()..].trim_start();
            if let Some(decl) = content.strip_prefix("interpretation ") {
                let name = decl.split(':').next().unwrap_or("").trim().to_string();
                assert!(
                    irtg.interpretation_ref(&name).is_some(),
                    "corpus declares interpretation {name:?} which the IRTG does not contain",
                );
                interpretation_order.push(name);
            }
            i += 1;
        } else {
            break; // first non-comment, non-blank line ends the header
        }
    }

    // --- instances -----------------------------------------------------------------------
    let n = interpretation_order.len();
    let block_size = n + usize::from(annotated);
    let mut instances = Vec::new();

    while i < all.len() {
        if limit.is_some_and(|l| instances.len() >= l) {
            break;
        }

        // An instance is the next `block_size` non-blank lines; blank lines are skipped
        // anywhere (Alto's flexible `readCorpus` mode).
        let mut block: Vec<usize> = Vec::with_capacity(block_size);
        while block.len() < block_size {
            while i < all.len() && all[i].trim().is_empty() {
                i += 1;
            }
            if i >= all.len() {
                break;
            }
            block.push(i);
            i += 1;
        }
        if block.is_empty() {
            break; // clean end of corpus
        }
        if block.len() != block_size {
            return Err(CorpusError::MalformedInstance {
                line: block[0] + 1,
                expected: block_size,
                found: block.len(),
            });
        }

        let mut objects = Vec::with_capacity(n);
        for (k, name) in interpretation_order.iter().enumerate() {
            let lineno = block[k];
            let text = &all[lineno];
            let interp = irtg
                .interpretation_ref(name)
                .expect("interpretation validated while reading the header");
            // Only parse interpretations that can be parse inputs; output-only interpretations
            // (e.g. tree algebras) keep their raw text and are evaluated into, not parsed from.
            let value = if interp.is_inputable() {
                Some(
                    interp
                        .parse_object_erased(text)
                        .map_err(|err| CorpusError::ObjectParse {
                            line: lineno + 1,
                            interpretation: name.clone(),
                            message: err.to_string(),
                        })?,
                )
            } else {
                None
            };
            objects.push(InterpObject {
                name: name.clone(),
                text: text.clone(),
                value,
            });
        }

        let gold_derivation = if annotated {
            let lineno = block[n];
            let mut arena = TreeArena::new();
            let root =
                parse_tree(&mut arena, &all[lineno]).map_err(|err| CorpusError::TreeParse {
                    line: lineno + 1,
                    message: err.to_string(),
                })?;
            Some((arena, root))
        } else {
            None
        };

        instances.push(Instance {
            objects,
            gold_derivation,
        });
    }

    Ok(Corpus {
        annotated,
        comment_prefix: marker,
        interpretation_order,
        instances,
    })
}

/// Streaming writer for an Alto corpus. Output is flushed after every instance so partial
/// results survive an interruption (the writer is not buffered).
pub struct CorpusWriter<W: Write> {
    writer: W,
    annotated: bool,
}

impl<W: Write> CorpusWriter<W> {
    /// Create a writer and emit the corpus header: version line, comment lines, interpretation
    /// declarations, and a trailing blank line. `prefix` is the comment prefix (e.g. `"# "`).
    pub fn new(
        mut writer: W,
        comment_lines: &[String],
        prefix: &str,
        interpretations: &[(String, String)],
        annotated: bool,
    ) -> io::Result<Self> {
        let kind = if annotated { "annotated" } else { "unannotated" };
        let blank = prefix.trim_end();
        writeln!(writer, "{prefix}IRTG {kind} corpus file, v1.0")?;
        writeln!(writer, "{blank}")?;
        for line in comment_lines {
            writeln!(writer, "{prefix}{line}")?;
        }
        writeln!(writer, "{blank}")?;
        for (name, class) in interpretations {
            writeln!(writer, "{prefix}interpretation {name}: {class}")?;
        }
        writeln!(writer)?;
        writer.flush()?;
        Ok(Self { writer, annotated })
    }

    /// Write one instance: the interpreted value of each interpretation (in `interp_order`),
    /// then (for annotated corpora) the derivation-tree line, then a blank separator.
    ///
    /// `derivation` is the best derivation tree (over grammar symbols) or `None` when the
    /// instance did not parse; in the latter case interpretation values are echoed from
    /// `fallback` and the derivation line is `_null_`. Flushes before returning.
    pub fn write_instance(
        &mut self,
        irtg: &Irtg,
        interp_order: &[String],
        derivation: Option<(&TreeArena<Symbol>, Tree)>,
        fallback: &Instance,
    ) -> io::Result<()> {
        for name in interp_order {
            let line = match derivation {
                Some((arena, root)) => irtg
                    .interpretation_ref(name)
                    .expect("interpretation present")
                    .interpret_to_string(arena, root)
                    .map_err(|err| io::Error::other(err.to_string()))?,
                None => fallback.text(name).unwrap_or(NULL_MARKER).to_string(),
            };
            writeln!(self.writer, "{line}")?;
        }

        if self.annotated {
            let tree_line = match derivation {
                Some((arena, root)) => {
                    let (resolved, resolved_root) = irtg.grammar_signature().resolve_tree(arena, root);
                    resolved_root.display(&resolved).to_string()
                }
                None => NULL_MARKER.to_string(),
            };
            writeln!(self.writer, "{tree_line}")?;
        }

        writeln!(self.writer)?;
        self.writer.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MaterializationStrategy, parse_irtg};

    const GRAMMAR: &str = "\
interpretation i: de.up.ling.irtg.algebra.StringAlgebra

S! -> r1(NP,VP)
  [i] *(?1,?2)
NP -> r2
  [i] john
NP -> r3
  [i] mary
VP -> r4(V,NP)
  [i] *(?1,?2)
V -> r5
  [i] watches
";

    fn parse_best(irtg: &Irtg, instance: &mut Instance) -> Option<crate::ViterbiTree> {
        let mut inputs = Vec::new();
        for obj in &mut instance.objects {
            let value = obj.value.take().unwrap();
            inputs.push(irtg.interpretation_ref(&obj.name).unwrap().input_erased(value));
        }
        irtg.best_with(inputs, &MaterializationStrategy::TopDownCondensed)
            .unwrap()
    }

    #[test]
    fn reads_unannotated_corpus() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let text = "# IRTG unannotated corpus file, v1.0\n\
                    # interpretation i: de.up.ling.irtg.algebra.StringAlgebra\n\n\
                    john watches mary\nmary watches john\n";
        let corpus = read_corpus(text.as_bytes(), &irtg, None).unwrap();

        assert!(!corpus.annotated);
        assert_eq!(corpus.comment_prefix, "#");
        assert_eq!(corpus.interpretation_order, vec!["i".to_string()]);
        assert_eq!(corpus.instances.len(), 2);
        assert_eq!(corpus.instances[0].text("i"), Some("john watches mary"));
    }

    #[test]
    fn limit_caps_instances() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let text = "# IRTG unannotated corpus file, v1.0\n\
                    # interpretation i: de.up.ling.irtg.algebra.StringAlgebra\n\n\
                    john watches mary\nmary watches john\n";
        let corpus = read_corpus(text.as_bytes(), &irtg, Some(1)).unwrap();
        assert_eq!(corpus.instances.len(), 1);
    }

    #[test]
    fn write_instance_emits_yield_and_tree() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let text = "# IRTG unannotated corpus file, v1.0\n\
                    # interpretation i: de.up.ling.irtg.algebra.StringAlgebra\n\n\
                    john watches mary\n";
        let mut corpus = read_corpus(text.as_bytes(), &irtg, None).unwrap();

        let best = parse_best(&irtg, &mut corpus.instances[0]);
        let tree = best.expect("parse should succeed");

        // The derivation tree interprets back to the input yield.
        let interp = irtg.interpretation_ref("i").unwrap();
        assert_eq!(
            interp.interpret_to_string(tree.arena(), tree.root()).unwrap(),
            "john watches mary",
        );

        let mut buf = Vec::new();
        let interps = vec![(
            "i".to_string(),
            "de.up.ling.irtg.algebra.StringAlgebra".to_string(),
        )];
        {
            let mut writer = CorpusWriter::new(&mut buf, &[], "# ", &interps, true).unwrap();
            writer
                .write_instance(
                    &irtg,
                    &corpus.interpretation_order,
                    Some((tree.arena(), tree.root())),
                    &corpus.instances[0],
                )
                .unwrap();
        }

        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("# IRTG annotated corpus file, v1.0"));
        assert!(out.contains("# interpretation i: de.up.ling.irtg.algebra.StringAlgebra"));
        assert!(out.contains("\njohn watches mary\n"));
        assert!(out.contains("r1(r2, r4(r5, r3))")); // S(NP=john, VP(V=watches, NP=mary))
    }

    #[test]
    fn write_instance_uses_null_marker_for_failed_parse() {
        let irtg = parse_irtg(GRAMMAR.as_bytes()).unwrap();
        let text = "# IRTG unannotated corpus file, v1.0\n\
                    # interpretation i: de.up.ling.irtg.algebra.StringAlgebra\n\n\
                    john watches mary\n";
        let corpus = read_corpus(text.as_bytes(), &irtg, None).unwrap();

        let mut buf = Vec::new();
        let interps = vec![(
            "i".to_string(),
            "de.up.ling.irtg.algebra.StringAlgebra".to_string(),
        )];
        {
            let mut writer = CorpusWriter::new(&mut buf, &[], "# ", &interps, true).unwrap();
            writer
                .write_instance(&irtg, &corpus.interpretation_order, None, &corpus.instances[0])
                .unwrap();
        }

        let out = String::from_utf8(buf).unwrap();
        assert!(out.contains("\njohn watches mary\n_null_\n")); // echoed input + null tree
    }
}
