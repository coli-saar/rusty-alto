//! Input codec for Alto's Tulipac TAG grammar format.
//!
//! The codec parses elementary trees, tree families, words, lemmas, feature
//! annotations, node markers, comments, and `#include` directives. It compiles
//! them into an [`Irtg`] with `string` and `tree` interpretations and, when
//! feature annotations occur, an `ft` feature-structure interpretation.

use crate::{
    CodecMetadata, InputCodec, InputCodecError, Irtg, IrtgError,
    alto_ast::{
        AstAutoRule, AstHomRule, AstHomTerm, AstInterpretationDecl, AstIrtg, AstRule, AstState,
    },
    irtg::build_irtg,
};
use packed_term_arena::tree::{Tree, TreeArena};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt, fs,
    io::Read,
    path::{Path, PathBuf},
};

const TAG_STRING_CLASS: &str = "de.up.ling.irtg.algebra.TagStringAlgebra";
const TAG_TREE_CLASS: &str = "de.up.ling.irtg.algebra.TagTreeAlgebra";
const FEATURE_STRUCTURE_CLASS: &str = "de.up.ling.irtg.algebra.FeatureStructureAlgebra";

const CONC11: &str = "*CONC11*";
const CONC12: &str = "*CONC12*";
const CONC21: &str = "*CONC21*";
const WRAP21: &str = "*WRAP21*";
const WRAP22: &str = "*WRAP22*";
const EE: &str = "*EE*";
const SUBSTITUTE: &str = "@";
const HOLE: &str = "*";

/// Alto-compatible reader for Tulipac `.tag` grammars.
#[derive(Clone, Debug, Default)]
pub struct TulipacInputCodec;

impl TulipacInputCodec {
    /// Construct a stateless Tulipac codec.
    pub fn new() -> Self {
        Self
    }

    fn read_path_inner(&self, path: &Path) -> Result<Irtg, TulipacError> {
        let mut declarations = Declarations::default();
        let mut include_stack = Vec::new();
        parse_path(path, &mut declarations, &mut include_stack)?;
        compile(declarations)
    }
}

impl InputCodec<Irtg> for TulipacInputCodec {
    fn metadata(&self) -> &'static CodecMetadata {
        static METADATA: CodecMetadata = CodecMetadata {
            name: "tulipac",
            description: "TAG grammar (Tulipac format)",
            extension: Some("tag"),
        };
        &METADATA
    }

    fn read(&self, reader: &mut dyn Read) -> Result<Irtg, InputCodecError> {
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes)?;
        let input = String::from_utf8(bytes)?;
        let declarations = Parser::new(&input)
            .and_then(Parser::parse_grammar)
            .map_err(InputCodecError::codec)?;
        if let Some(include) = declarations.includes.first() {
            return Err(InputCodecError::codec(TulipacError::Semantic(format!(
                "#include {include:?} requires TulipacInputCodec::read_path"
            ))));
        }
        compile(declarations).map_err(InputCodecError::codec)
    }

    fn read_path(&self, path: &Path) -> Result<Irtg, InputCodecError> {
        self.read_path_inner(path).map_err(InputCodecError::codec)
    }
}

/// Failure while reading, parsing, validating, or compiling a Tulipac grammar.
#[derive(Debug)]
pub enum TulipacError {
    /// A grammar or included file could not be read.
    Io {
        /// Path that could not be read.
        path: PathBuf,
        /// Underlying filesystem error.
        source: std::io::Error,
    },
    /// Tokenization failed.
    Lex {
        /// UTF-8 byte offset of the offending input.
        offset: usize,
        /// Human-readable diagnostic.
        message: String,
    },
    /// The token stream did not match the Tulipac grammar.
    Parse {
        /// UTF-8 byte offset of the offending token.
        offset: usize,
        /// Human-readable diagnostic.
        message: String,
    },
    /// Declarations were syntactically valid but inconsistent.
    Semantic(String),
    /// Conversion to rusty-alto's IRTG representation failed.
    Irtg(IrtgError),
}

impl fmt::Display for TulipacError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "cannot read {}: {source}", path.display()),
            Self::Lex { offset, message } => {
                write!(f, "Tulipac lexical error at byte {offset}: {message}")
            }
            Self::Parse { offset, message } => {
                write!(f, "Tulipac syntax error at byte {offset}: {message}")
            }
            Self::Semantic(message) => write!(f, "invalid Tulipac grammar: {message}"),
            Self::Irtg(error) => write!(f, "cannot construct IRTG: {error}"),
        }
    }
}

impl std::error::Error for TulipacError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Irtg(error) => Some(error),
            _ => None,
        }
    }
}

impl From<IrtgError> for TulipacError {
    fn from(value: IrtgError) -> Self {
        Self::Irtg(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Tree,
    Family,
    Word,
    Lemma,
    Include,
    Name(String),
    FamilyName(String),
    Annotation(String),
    Variable(String),
    Bang,
    Star,
    Plus,
    Colon,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Equals,
}

#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
    offset: usize,
}

fn lex(input: &str) -> Result<Vec<Token>, TulipacError> {
    let mut tokens = Vec::new();
    let mut chars = input.char_indices().peekable();

    while let Some((offset, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        if ch == '/' && chars.peek().is_some_and(|&(_, next)| next == '/') {
            chars.next();
            for (_, next) in chars.by_ref() {
                if next == '\n' {
                    break;
                }
            }
            continue;
        }
        if ch == '/' && chars.peek().is_some_and(|&(_, next)| next == '*') {
            chars.next();
            let mut previous = '\0';
            let mut closed = false;
            for (_, next) in chars.by_ref() {
                if previous == '*' && next == '/' {
                    closed = true;
                    break;
                }
                previous = next;
            }
            if !closed {
                return Err(TulipacError::Lex {
                    offset,
                    message: "unterminated block comment".to_owned(),
                });
            }
            continue;
        }

        let kind = match ch {
            '\'' | '"' => {
                let quote = ch;
                let mut value = String::new();
                let mut closed = false;
                for (_, next) in chars.by_ref() {
                    if next == quote {
                        closed = true;
                        break;
                    }
                    value.push(next);
                }
                if !closed {
                    return Err(TulipacError::Lex {
                        offset,
                        message: "unterminated quoted identifier".to_owned(),
                    });
                }
                TokenKind::Name(value)
            }
            '<' => {
                let mut value = String::new();
                let mut closed = false;
                for (_, next) in chars.by_ref() {
                    if next == '>' {
                        closed = true;
                        break;
                    }
                    value.push(next);
                }
                if !closed {
                    return Err(TulipacError::Lex {
                        offset,
                        message: "unterminated family identifier".to_owned(),
                    });
                }
                TokenKind::FamilyName(value)
            }
            '@' | '?' => {
                let mut value = String::new();
                while let Some(&(_, next)) = chars.peek() {
                    if next.is_ascii_alphanumeric() || next == '_' {
                        value.push(next);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if value.is_empty() {
                    return Err(TulipacError::Lex {
                        offset,
                        message: format!("{ch} must be followed by an identifier"),
                    });
                }
                if ch == '@' {
                    TokenKind::Annotation(value)
                } else {
                    TokenKind::Variable(value)
                }
            }
            '#' => {
                let mut word = String::from("#");
                while let Some(&(_, next)) = chars.peek() {
                    if next.is_ascii_alphabetic() {
                        word.push(next);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if word == "#include" {
                    TokenKind::Include
                } else {
                    return Err(TulipacError::Lex {
                        offset,
                        message: format!("unknown directive {word:?}"),
                    });
                }
            }
            '!' => TokenKind::Bang,
            '*' => TokenKind::Star,
            '+' => TokenKind::Plus,
            ':' => TokenKind::Colon,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            ',' => TokenKind::Comma,
            '=' => TokenKind::Equals,
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut value = String::new();
                value.push(c);
                while let Some(&(_, next)) = chars.peek() {
                    if next.is_ascii_alphanumeric() || next == '_' {
                        value.push(next);
                        chars.next();
                    } else {
                        break;
                    }
                }
                match value.as_str() {
                    "tree" => TokenKind::Tree,
                    "family" => TokenKind::Family,
                    "word" => TokenKind::Word,
                    "lemma" => TokenKind::Lemma,
                    _ => TokenKind::Name(value),
                }
            }
            _ => {
                return Err(TulipacError::Lex {
                    offset,
                    message: format!("unexpected character {ch:?}"),
                });
            }
        };
        tokens.push(Token { kind, offset });
    }

    Ok(tokens)
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct FeatureMap(BTreeMap<String, FeatureAtom>);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum FeatureAtom {
    Constant(String),
    Variable(String),
}

impl FeatureMap {
    fn merge(&self, other: &Self) -> Result<Self, TulipacError> {
        let mut result = self.0.clone();
        for (attribute, value) in &other.0 {
            match (result.get(attribute), value) {
                (None, _) => {
                    result.insert(attribute.clone(), value.clone());
                }
                (Some(existing), candidate) if existing == candidate => {}
                (Some(FeatureAtom::Variable(_)), candidate) => {
                    result.insert(attribute.clone(), candidate.clone());
                }
                (Some(_), FeatureAtom::Variable(_)) => {}
                (Some(existing), candidate) => {
                    return Err(TulipacError::Semantic(format!(
                        "feature clash for {attribute:?}: {existing:?} versus {candidate:?}"
                    )));
                }
            }
        }
        Ok(Self(result))
    }

    fn safe_suffix(&self) -> String {
        if self.0.is_empty() {
            return String::new();
        }
        let mut raw = String::new();
        for (attribute, value) in &self.0 {
            raw.push('[');
            raw.push_str(attribute);
            raw.push('=');
            match value {
                FeatureAtom::Constant(value) => raw.push_str(value),
                FeatureAtom::Variable(value) => {
                    raw.push('?');
                    raw.push_str(value);
                }
            }
            raw.push(']');
        }
        raw.chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NodeType {
    Default,
    Substitution,
    Foot,
    Head,
}

#[derive(Clone, Debug)]
struct Node {
    label: String,
    node_type: NodeType,
    no_adjunction: bool,
    top: Option<FeatureMap>,
    bottom: Option<FeatureMap>,
}

#[derive(Debug)]
struct ElementaryTree {
    arena: TreeArena<Node>,
    root: Tree,
}

impl ElementaryTree {
    fn is_auxiliary(&self) -> bool {
        self.arena
            .post_order(self.root)
            .any(|node| self.arena.get_label(node).node_type == NodeType::Foot)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LexiconEntry {
    word: String,
    tree: String,
    features: FeatureMap,
}

#[derive(Debug, Default)]
struct Declarations {
    trees: Vec<(String, ElementaryTree)>,
    families: Vec<(String, Vec<String>)>,
    words: Vec<WordDecl>,
    lemmas: Vec<LemmaDecl>,
    includes: Vec<String>,
}

impl Declarations {
    fn extend(&mut self, mut other: Self) {
        self.trees.append(&mut other.trees);
        self.families.append(&mut other.families);
        self.words.append(&mut other.words);
        self.lemmas.append(&mut other.lemmas);
        self.includes.append(&mut other.includes);
    }
}

#[derive(Clone, Debug)]
enum TreeRef {
    Tree(String),
    Family(String),
}

#[derive(Clone, Debug)]
struct WordDecl {
    word: String,
    target: TreeRef,
    features: FeatureMap,
}

#[derive(Clone, Debug)]
struct LemmaDecl {
    lemma: String,
    target: TreeRef,
    features: FeatureMap,
    words: Vec<(String, FeatureMap)>,
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn new(input: &str) -> Result<Self, TulipacError> {
        Ok(Self {
            tokens: lex(input)?,
            position: 0,
        })
    }

    fn parse_grammar(mut self) -> Result<Declarations, TulipacError> {
        let mut declarations = Declarations::default();
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Tree => declarations.trees.push(self.parse_tree()?),
                TokenKind::Family => declarations.families.push(self.parse_family()?),
                TokenKind::Word => declarations.words.push(self.parse_word()?),
                TokenKind::Lemma => declarations.lemmas.push(self.parse_lemma()?),
                TokenKind::Include => declarations.includes.push(self.parse_include()?),
                _ => return self.error("expected tree, family, word, lemma, or #include"),
            }
        }
        Ok(declarations)
    }

    fn parse_tree(&mut self) -> Result<(String, ElementaryTree), TulipacError> {
        self.expect_simple(TokenKind::Tree)?;
        let name = self.identifier()?;
        self.expect_simple(TokenKind::Colon)?;
        let mut arena = TreeArena::new();
        let root = self.node(&mut arena)?;
        Ok((name, ElementaryTree { arena, root }))
    }

    fn node(&mut self, arena: &mut TreeArena<Node>) -> Result<Tree, TulipacError> {
        let label = self.identifier()?;
        let node_type = match self.peek().map(|token| &token.kind) {
            Some(TokenKind::Bang) => {
                self.position += 1;
                NodeType::Substitution
            }
            Some(TokenKind::Star) => {
                self.position += 1;
                NodeType::Foot
            }
            Some(TokenKind::Plus) => {
                self.position += 1;
                NodeType::Head
            }
            _ => NodeType::Default,
        };
        let no_adjunction = match self.peek().map(|token| &token.kind) {
            Some(TokenKind::Annotation(annotation)) => {
                let no_adjunction = annotation == "NA";
                self.position += 1;
                no_adjunction
            }
            _ => false,
        };
        let top = if self.at(&TokenKind::LBracket) {
            Some(self.feature_map()?)
        } else {
            None
        };
        let bottom = if self.at(&TokenKind::LBracket) {
            Some(self.feature_map()?)
        } else {
            None
        };
        let mut children = Vec::new();
        if self.consume(&TokenKind::LBrace) {
            while !self.consume(&TokenKind::RBrace) {
                if self.peek().is_none() {
                    return self.error("unterminated node child block");
                }
                children.push(self.node(arena)?);
            }
        }
        Ok(arena.add_node(
            Node {
                label,
                node_type,
                no_adjunction,
                top,
                bottom,
            },
            children,
        ))
    }

    fn parse_family(&mut self) -> Result<(String, Vec<String>), TulipacError> {
        self.expect_simple(TokenKind::Family)?;
        let name = self.identifier()?;
        self.expect_simple(TokenKind::Colon)?;
        self.expect_simple(TokenKind::LBrace)?;
        let mut trees = vec![self.identifier()?];
        while self.consume(&TokenKind::Comma) {
            trees.push(self.identifier()?);
        }
        self.expect_simple(TokenKind::RBrace)?;
        Ok((name, trees))
    }

    fn parse_word(&mut self) -> Result<WordDecl, TulipacError> {
        self.expect_simple(TokenKind::Word)?;
        let word = self.identifier()?;
        self.expect_simple(TokenKind::Colon)?;
        let target = self.tree_ref()?;
        let features = if self.at(&TokenKind::LBracket) {
            self.feature_map()?
        } else {
            FeatureMap::default()
        };
        Ok(WordDecl {
            word,
            target,
            features,
        })
    }

    fn parse_lemma(&mut self) -> Result<LemmaDecl, TulipacError> {
        self.expect_simple(TokenKind::Lemma)?;
        let lemma = self.identifier()?;
        self.expect_simple(TokenKind::Colon)?;
        let target = self.tree_ref()?;
        let features = if self.at(&TokenKind::LBracket) {
            self.feature_map()?
        } else {
            FeatureMap::default()
        };
        self.expect_simple(TokenKind::LBrace)?;
        let mut words = Vec::new();
        while !self.consume(&TokenKind::RBrace) {
            self.expect_simple(TokenKind::Word)?;
            let word = self.identifier()?;
            let word_features = if self.consume(&TokenKind::Colon) {
                self.feature_map()?
            } else {
                FeatureMap::default()
            };
            words.push((word, word_features));
        }
        if words.is_empty() {
            return self.error("lemma must contain at least one word");
        }
        Ok(LemmaDecl {
            lemma,
            target,
            features,
            words,
        })
    }

    fn parse_include(&mut self) -> Result<String, TulipacError> {
        self.expect_simple(TokenKind::Include)?;
        self.identifier()
    }

    fn feature_map(&mut self) -> Result<FeatureMap, TulipacError> {
        self.expect_simple(TokenKind::LBracket)?;
        let mut features = BTreeMap::new();
        if self.consume(&TokenKind::RBracket) {
            return Ok(FeatureMap(features));
        }
        loop {
            let attribute = self.identifier()?;
            self.expect_simple(TokenKind::Equals)?;
            let value = match self.next() {
                Some(Token {
                    kind: TokenKind::Name(value),
                    ..
                }) => FeatureAtom::Constant(value),
                Some(Token {
                    kind: TokenKind::Variable(value),
                    ..
                }) => FeatureAtom::Variable(value),
                Some(token) => {
                    return Err(TulipacError::Parse {
                        offset: token.offset,
                        message: "expected feature value or variable".to_owned(),
                    });
                }
                None => return self.error("expected feature value or variable"),
            };
            features.insert(attribute, value);
            if self.consume(&TokenKind::RBracket) {
                break;
            }
            self.expect_simple(TokenKind::Comma)?;
        }
        Ok(FeatureMap(features))
    }

    fn tree_ref(&mut self) -> Result<TreeRef, TulipacError> {
        match self.next() {
            Some(Token {
                kind: TokenKind::Name(name),
                ..
            }) => Ok(TreeRef::Tree(name)),
            Some(Token {
                kind: TokenKind::FamilyName(name),
                ..
            }) => Ok(TreeRef::Family(name)),
            Some(token) => Err(TulipacError::Parse {
                offset: token.offset,
                message: "expected elementary-tree or family name".to_owned(),
            }),
            None => self.error("expected elementary-tree or family name"),
        }
    }

    fn identifier(&mut self) -> Result<String, TulipacError> {
        match self.next() {
            Some(Token {
                kind: TokenKind::Name(name),
                ..
            }) => Ok(name),
            Some(token) => Err(TulipacError::Parse {
                offset: token.offset,
                message: "expected identifier".to_owned(),
            }),
            None => self.error("expected identifier"),
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned();
        if token.is_some() {
            self.position += 1;
        }
        token
    }

    fn at(&self, kind: &TokenKind) -> bool {
        self.peek().is_some_and(|token| &token.kind == kind)
    }

    fn consume(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn expect_simple(&mut self, kind: TokenKind) -> Result<(), TulipacError> {
        match self.next() {
            Some(token) if token.kind == kind => Ok(()),
            Some(token) => Err(TulipacError::Parse {
                offset: token.offset,
                message: format!("expected {kind:?}, found {:?}", token.kind),
            }),
            None => self.error(&format!("expected {kind:?}")),
        }
    }

    fn error<T>(&self, message: &str) -> Result<T, TulipacError> {
        Err(TulipacError::Parse {
            offset: self.peek().map_or(0, |token| token.offset),
            message: message.to_owned(),
        })
    }
}

fn parse_path(
    path: &Path,
    declarations: &mut Declarations,
    include_stack: &mut Vec<PathBuf>,
) -> Result<(), TulipacError> {
    let canonical = path.canonicalize().map_err(|source| TulipacError::Io {
        path: path.to_owned(),
        source,
    })?;
    if include_stack.contains(&canonical) {
        return Err(TulipacError::Semantic(format!(
            "cyclic #include involving {}",
            canonical.display()
        )));
    }
    include_stack.push(canonical.clone());
    let input = fs::read_to_string(&canonical).map_err(|source| TulipacError::Io {
        path: canonical.clone(),
        source,
    })?;
    let mut parsed = Parser::new(&input)?.parse_grammar()?;
    let base = canonical.parent().unwrap_or_else(|| Path::new("."));
    for include in std::mem::take(&mut parsed.includes) {
        parse_path(&base.join(include), declarations, include_stack)?;
    }
    declarations.extend(parsed);
    include_stack.pop();
    Ok(())
}

fn compile(declarations: Declarations) -> Result<Irtg, TulipacError> {
    let mut trees = HashMap::new();
    for (name, tree) in declarations.trees {
        trees.insert(name, tree);
    }
    let mut families = HashMap::new();
    for (name, members) in declarations.families {
        families.insert(name, members);
    }

    let resolve = |target: &TreeRef, context: &str| -> Result<Vec<String>, TulipacError> {
        match target {
            TreeRef::Tree(tree) => {
                if trees.contains_key(tree) {
                    Ok(vec![tree.clone()])
                } else {
                    Err(TulipacError::Semantic(format!(
                        "{context} references unknown elementary tree {tree:?}"
                    )))
                }
            }
            TreeRef::Family(family) => {
                let members = families.get(family).ok_or_else(|| {
                    TulipacError::Semantic(format!(
                        "{context} references unknown tree family {family:?}"
                    ))
                })?;
                for tree in members {
                    if !trees.contains_key(tree) {
                        return Err(TulipacError::Semantic(format!(
                            "{context} references family {family:?}, which contains unknown tree {tree:?}"
                        )));
                    }
                }
                Ok(members.clone())
            }
        }
    };

    let mut lexicon = HashSet::new();
    for word in declarations.words {
        for tree in resolve(&word.target, &format!("word {:?}", word.word))? {
            lexicon.insert(LexiconEntry {
                word: word.word.clone(),
                tree,
                features: word.features.clone(),
            });
        }
    }
    for lemma in declarations.lemmas {
        let tree_names = resolve(&lemma.target, &format!("lemma {:?}", lemma.lemma))?;
        for (word, word_features) in lemma.words {
            let features = lemma.features.merge(&word_features)?;
            for tree in &tree_names {
                lexicon.insert(LexiconEntry {
                    word: word.clone(),
                    tree: tree.clone(),
                    features: features.clone(),
                });
            }
        }
    }

    let has_features = trees.values().any(|tree| {
        tree.arena.post_order(tree.root).any(|node| {
            let node = tree.arena.get_label(node);
            node.top.is_some() || node.bottom.is_some()
        })
    });
    let mut rules = Vec::new();
    let mut adjunction_states = BTreeSet::new();
    for entry in lexicon {
        let tree = &trees[&entry.tree];
        let mut child_states = Vec::new();
        let tree_hom = tree_term(
            tree,
            tree.root,
            &entry,
            &mut child_states,
            &mut adjunction_states,
        );
        let string_hom = string_term(&tree_hom, &child_states)?;
        let feature_hom = has_features
            .then(|| feature_term(tree, &tree_hom, &child_states, &entry))
            .transpose()?;
        let parent = if tree.is_auxiliary() {
            state_name(&tree.arena.get_label(tree.root).label, 'A')
        } else {
            state_name(&tree.arena.get_label(tree.root).label, 'S')
        };
        let symbol = format!(
            "{}-{}{}",
            entry.tree,
            entry.word,
            entry.features.safe_suffix()
        );
        rules.push(AstRule {
            auto: AstAutoRule {
                parent: AstState {
                    name: parent,
                    is_final: false,
                },
                symbol,
                children: child_states
                    .iter()
                    .map(|name| AstState {
                        name: name.clone(),
                        is_final: false,
                    })
                    .collect(),
                weight: None,
            },
            homs: {
                let mut homs = vec![
                    AstHomRule {
                        interpretation: "tree".to_owned(),
                        term: tree_hom,
                    },
                    AstHomRule {
                        interpretation: "string".to_owned(),
                        term: string_hom,
                    },
                ];
                if let Some(term) = feature_hom {
                    homs.push(AstHomRule {
                        interpretation: "ft".to_owned(),
                        term,
                    });
                }
                homs
            },
        });
    }

    for state in adjunction_states {
        rules.push(AstRule {
            auto: AstAutoRule {
                parent: AstState {
                    name: state.clone(),
                    is_final: false,
                },
                symbol: format!("*NOP*_{state}"),
                children: Vec::new(),
                weight: None,
            },
            homs: {
                let mut homs = vec![
                    AstHomRule {
                        interpretation: "tree".to_owned(),
                        term: AstHomTerm::Symbol(HOLE.to_owned(), Vec::new()),
                    },
                    AstHomRule {
                        interpretation: "string".to_owned(),
                        term: AstHomTerm::Symbol(EE.to_owned(), Vec::new()),
                    },
                ];
                if has_features {
                    homs.push(AstHomRule {
                        interpretation: "ft".to_owned(),
                        term: AstHomTerm::Symbol("[foot: #1 [], root: #1]".to_owned(), Vec::new()),
                    });
                }
                homs
            },
        });
    }

    if !rules.iter().any(|rule| rule.auto.parent.name == "S_S") {
        return Err(TulipacError::Semantic(
            "grammar has no initial tree rooted in S".to_owned(),
        ));
    }
    for rule in &mut rules {
        if rule.auto.parent.name == "S_S" {
            rule.auto.parent.is_final = true;
        }
    }

    build_irtg(AstIrtg {
        interpretations: {
            let mut interpretations = vec![
                AstInterpretationDecl {
                    name: "string".to_owned(),
                    algebra: TAG_STRING_CLASS.to_owned(),
                },
                AstInterpretationDecl {
                    name: "tree".to_owned(),
                    algebra: TAG_TREE_CLASS.to_owned(),
                },
            ];
            if has_features {
                interpretations.push(AstInterpretationDecl {
                    name: "ft".to_owned(),
                    algebra: FEATURE_STRUCTURE_CLASS.to_owned(),
                });
            }
            interpretations
        },
        features: Vec::new(),
        rules,
    })
    .map_err(Into::into)
}

fn state_name(label: &str, sort: char) -> String {
    format!("{label}_{sort}")
}

fn tree_term(
    tree: &ElementaryTree,
    node: Tree,
    entry: &LexiconEntry,
    child_states: &mut Vec<String>,
    adjunction_states: &mut BTreeSet<String>,
) -> AstHomTerm {
    let data = tree.arena.get_label(node);
    let mut children: Vec<_> = tree
        .arena
        .get_children(node)
        .iter()
        .map(|&child| tree_term(tree, child, entry, child_states, adjunction_states))
        .collect();

    match data.node_type {
        NodeType::Head => {
            children = vec![AstHomTerm::Symbol(entry.word.clone(), Vec::new())];
            ordinary_or_adjunction(data, children, child_states, adjunction_states)
        }
        NodeType::Foot => AstHomTerm::Symbol(HOLE.to_owned(), Vec::new()),
        NodeType::Substitution => {
            child_states.push(state_name(&data.label, 'S'));
            AstHomTerm::Variable(child_states.len())
        }
        NodeType::Default => {
            ordinary_or_adjunction(data, children, child_states, adjunction_states)
        }
    }
}

fn ordinary_or_adjunction(
    node: &Node,
    children: Vec<AstHomTerm>,
    child_states: &mut Vec<String>,
    adjunction_states: &mut BTreeSet<String>,
) -> AstHomTerm {
    let ordinary = AstHomTerm::Symbol(format!("{}_{}", node.label, children.len()), children);
    if node.no_adjunction {
        ordinary
    } else {
        let state = state_name(&node.label, 'A');
        child_states.push(state.clone());
        adjunction_states.insert(state);
        AstHomTerm::Symbol(
            SUBSTITUTE.to_owned(),
            vec![AstHomTerm::Variable(child_states.len()), ordinary],
        )
    }
}

#[derive(Clone, Debug)]
struct SortedTerm {
    term: AstHomTerm,
    sort: u8,
}

fn string_term(
    tree_term: &AstHomTerm,
    child_states: &[String],
) -> Result<AstHomTerm, TulipacError> {
    fn convert(term: &AstHomTerm, child_states: &[String]) -> Result<SortedTerm, TulipacError> {
        match term {
            AstHomTerm::Variable(variable) => {
                let state = child_states.get(variable - 1).ok_or_else(|| {
                    TulipacError::Semantic(format!("invalid variable ?{variable}"))
                })?;
                Ok(SortedTerm {
                    term: term.clone(),
                    sort: if state.ends_with("_S") { 1 } else { 2 },
                })
            }
            AstHomTerm::Symbol(label, children) if label == SUBSTITUTE => {
                let converted = children
                    .iter()
                    .map(|child| convert(child, child_states))
                    .collect::<Result<Vec<_>, _>>()?;
                let operation = match (converted[0].sort, converted[1].sort) {
                    (2, 1) => WRAP21,
                    (2, 2) => WRAP22,
                    sorts => {
                        return Err(TulipacError::Semantic(format!(
                            "invalid TAG wrap sorts {sorts:?}"
                        )));
                    }
                };
                Ok(SortedTerm {
                    term: AstHomTerm::Symbol(
                        operation.to_owned(),
                        converted.into_iter().map(|term| term.term).collect(),
                    ),
                    sort: if operation == WRAP21 { 1 } else { 2 },
                })
            }
            AstHomTerm::Symbol(label, children) if label == HOLE => Ok(SortedTerm {
                term: AstHomTerm::Symbol(EE.to_owned(), Vec::new()),
                sort: 2,
            }),
            AstHomTerm::Symbol(label, children) => {
                let mut converted = children
                    .iter()
                    .map(|child| convert(child, child_states))
                    .collect::<Result<Vec<_>, _>>()?;
                match converted.len() {
                    0 => Ok(SortedTerm {
                        term: AstHomTerm::Symbol(label.clone(), Vec::new()),
                        sort: 1,
                    }),
                    1 => Ok(converted.remove(0)),
                    _ => concatenate(&converted),
                }
            }
        }
    }

    fn concatenate(children: &[SortedTerm]) -> Result<SortedTerm, TulipacError> {
        let left = children[0].clone();
        let right = if children.len() == 2 {
            children[1].clone()
        } else {
            concatenate(&children[1..])?
        };
        let (operation, sort) = match (left.sort, right.sort) {
            (1, 1) => (CONC11, 1),
            (1, 2) => (CONC12, 2),
            (2, 1) => (CONC21, 2),
            sorts => {
                return Err(TulipacError::Semantic(format!(
                    "cannot concatenate TAG string sorts {sorts:?}"
                )));
            }
        };
        Ok(SortedTerm {
            term: AstHomTerm::Symbol(operation.to_owned(), vec![left.term, right.term]),
            sort,
        })
    }

    Ok(convert(tree_term, child_states)?.term)
}

fn feature_term(
    tree: &ElementaryTree,
    tree_term: &AstHomTerm,
    child_states: &[String],
    entry: &LexiconEntry,
) -> Result<AstHomTerm, TulipacError> {
    let mut node_ids = HashMap::new();
    let mut next_id = 1usize;
    for node in tree.arena.post_order(tree.root) {
        let id = if tree.arena.get_label(node).node_type == NodeType::Foot {
            "foot".to_owned()
        } else {
            let id = format!("n{next_id}");
            next_id += 1;
            id
        };
        node_ids.insert(node, id);
    }

    let mut child_nodes = Vec::new();
    collect_feature_children(tree, tree.root, &node_ids, &mut child_nodes);
    if child_nodes.len() != child_states.len() {
        return Err(TulipacError::Semantic(
            "internal child ordering mismatch while building feature homomorphism".to_owned(),
        ));
    }
    let core = core_feature_literal(tree, &node_ids, entry)?;

    fn convert(
        term: &AstHomTerm,
        child_states: &[String],
        child_nodes: &[String],
        core: &str,
    ) -> Result<AstHomTerm, TulipacError> {
        match term {
            AstHomTerm::Variable(variable) => {
                let index = variable - 1;
                let node = child_nodes.get(index).ok_or_else(|| {
                    TulipacError::Semantic(format!("invalid feature variable ?{variable}"))
                })?;
                let state = &child_states[index];
                if state.ends_with("_S") {
                    Ok(AstHomTerm::Symbol(
                        format!("emb_{node}"),
                        vec![AstHomTerm::Symbol(
                            "proj_root".to_owned(),
                            vec![term.clone()],
                        )],
                    ))
                } else {
                    Ok(AstHomTerm::Symbol(
                        format!("remap_root={node}t,foot={node}b"),
                        vec![term.clone()],
                    ))
                }
            }
            AstHomTerm::Symbol(label, children) if children.is_empty() => {
                if label == HOLE {
                    Ok(AstHomTerm::Symbol("[]".to_owned(), Vec::new()))
                } else {
                    Ok(AstHomTerm::Symbol(core.to_owned(), Vec::new()))
                }
            }
            AstHomTerm::Symbol(_, children) => {
                let converted = children
                    .iter()
                    .map(|child| convert(child, child_states, child_nodes, core))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut iter = converted.into_iter().rev();
                let mut result = iter.next().unwrap();
                for child in iter {
                    result = AstHomTerm::Symbol("unify".to_owned(), vec![result, child]);
                }
                Ok(result)
            }
        }
    }

    convert(tree_term, child_states, &child_nodes, &core)
}

fn collect_feature_children(
    tree: &ElementaryTree,
    node: Tree,
    node_ids: &HashMap<Tree, String>,
    out: &mut Vec<String>,
) {
    for &child in tree.arena.get_children(node) {
        collect_feature_children(tree, child, node_ids, out);
    }
    let data = tree.arena.get_label(node);
    match data.node_type {
        NodeType::Substitution => out.push(node_ids[&node].clone()),
        NodeType::Foot => {}
        NodeType::Default | NodeType::Head if !data.no_adjunction => {
            out.push(node_ids[&node].clone())
        }
        NodeType::Default | NodeType::Head => {}
    }
}

fn core_feature_literal(
    tree: &ElementaryTree,
    node_ids: &HashMap<Tree, String>,
    entry: &LexiconEntry,
) -> Result<String, TulipacError> {
    let mut attributes = Vec::<(String, FeatureMap)>::new();
    let mut root_top = None;

    for node in tree.arena.post_order(tree.root) {
        let data = tree.arena.get_label(node);
        let id = &node_ids[&node];
        match data.node_type {
            NodeType::Foot => {
                attributes.push((id.clone(), data.top.clone().unwrap_or_default()));
            }
            NodeType::Substitution => {
                attributes.push((id.clone(), data.top.clone().unwrap_or_default()));
            }
            NodeType::Default | NodeType::Head => {
                let top_name = format!("{id}t");
                let bottom_name = format!("{id}b");
                let bottom = if data.node_type == NodeType::Head {
                    data.bottom
                        .clone()
                        .unwrap_or_default()
                        .merge(&entry.features)?
                } else {
                    data.bottom.clone().unwrap_or_default()
                };
                attributes.push((top_name.clone(), data.top.clone().unwrap_or_default()));
                attributes.push((bottom_name, bottom));
                if node == tree.root {
                    root_top = Some(top_name);
                }
            }
        }
    }

    let root_top = root_top.ok_or_else(|| {
        TulipacError::Semantic(
            "elementary-tree root cannot be a foot or substitution node".to_owned(),
        )
    })?;
    let mut defined = HashSet::new();
    let mut fields = Vec::new();
    for (attribute, features) in attributes {
        let mut value = feature_map_literal(&features, &mut defined);
        if attribute == root_top {
            value = format!("#__root {value}");
            defined.insert("__root".to_owned());
        }
        fields.push(format!("{attribute}: {value}"));
    }
    fields.push("root: #__root".to_owned());
    Ok(format!("[{}]", fields.join(", ")))
}

fn feature_map_literal(features: &FeatureMap, defined: &mut HashSet<String>) -> String {
    let fields = features
        .0
        .iter()
        .map(|(attribute, value)| {
            let value = match value {
                FeatureAtom::Constant(value) => value.clone(),
                FeatureAtom::Variable(variable) => {
                    if defined.insert(variable.clone()) {
                        format!("#{variable}")
                    } else {
                        format!("#{variable}")
                    }
                }
            };
            format!("{attribute}: {value}")
        })
        .collect::<Vec<_>>();
    format!("[{}]", fields.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Binarizing, TagStringAlgebra, TagTreeAlgebra};

    const CHASING: &str = r#"
        tree trans:
          S {
            NP![case=nom][]
            VP {
              V+
              NP![case=acc][]
            }
          }

        tree np_n:
          NP[][case=?case] {
            Det! [case=?case][]
            N+ [case=?case][]
          }

        tree det:
          Det+

        word 'jagt': trans
        word 'hund': np_n[case=nom]
        word 'hasen': np_n[case=acc]
        word 'der': det[case=nom]
        word 'den': det[case=acc]
    "#;

    const ADJUNCTION: &str = r#"
        tree clause:
          S @NA {
            NP!
            VP {
              V+ @NA
            }
          }

        tree noun:
          NP @NA {
            N+ @NA
          }

        tree adverb:
          VP @NA {
            Adv+ @NA
            VP*
          }

        word 'john': noun
        word 'sleeps': clause
        word 'quickly': adverb
    "#;

    const RECURSIVE_ADJUNCTION: &str = r#"
        tree seed:
          S @NA {
            VP {
              Center+ @NA
            }
          }

        tree copy:
          VP {
            Left+ @NA
            VP*
            Right+ @NA
          }

        word 'c': seed
        word 'a': copy
    "#;

    const SHIEBER: &str = r#"
        family vinf_tv: { vinf_tv, vinf_tv_aux }
        tree vinf_tv:
          S @NA {
            np! [case=nom][]
            S { np! [case=?o] [] }
            v+ [objcase=?o] []
          }
        tree vinf_tv_aux:
          S @NA {
            S { S @NA { np! [case=?o] [] S* } }
            v+ [objcase=?o][]
          }
        family np_n: { np_n }
        tree np_n:
          np [] [case=?c] { n+ [case=?c] [] }
        tree adj_det:
          np [] [case=?c] {
            det+ [case=?c] []
            np* [case=?c] []
          }
        word 'de': adj_det[case=acc]
        word 'huus': np_n
        word 'aastriiche': <vinf_tv>[objcase=acc]
        word 'laa': <vinf_tv>[objcase=acc]
    "#;

    fn best_derivation(irtg: &Irtg, sentence: &str) -> String {
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();
        let value = string.parse_object(sentence).unwrap();
        let best = irtg
            .parse([string.input(value)])
            .unwrap()
            .automaton
            .viterbi()
            .unwrap();
        irtg.resolve_derivation(best.arena(), best.root())
            .to_string()
    }

    #[test]
    fn reads_and_parses_tulipac_grammar() {
        let irtg = TulipacInputCodec.decode(CHASING).unwrap();
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();
        let value = string.parse_object("der hund jagt den hasen").unwrap();
        assert!(
            irtg.parse([string.input(value)])
                .unwrap()
                .automaton
                .viterbi()
                .is_some()
        );
        assert!(irtg.interpretation::<TagTreeAlgebra>("tree").is_ok());
    }

    #[test]
    fn parses_tulipac_adjunction_with_exact_derivations() {
        let irtg = TulipacInputCodec.decode(ADJUNCTION).unwrap();

        assert_eq!(
            best_derivation(&irtg, "john sleeps"),
            "clause-sleeps(noun-john, '*NOP*_VP_A')"
        );
        assert_eq!(
            best_derivation(&irtg, "john quickly sleeps"),
            "clause-sleeps(noun-john, adverb-quickly)"
        );
    }

    #[test]
    fn recursively_adjoins_an_auxiliary_tree_around_its_foot() {
        let irtg = TulipacInputCodec.decode(RECURSIVE_ADJUNCTION).unwrap();

        assert_eq!(
            best_derivation(&irtg, "a a c a a"),
            "seed-c(copy-a(copy-a('*NOP*_VP_A')))"
        );
    }

    #[test]
    fn supports_families_lemmas_and_no_adjunction() {
        let irtg = TulipacInputCodec
            .decode(
                r#"
                family verbs: { v }
                tree v: S @NA { V+ }
                lemma 'sleep': <verbs> [tense=pres] {
                  word 'sleeps'
                }
                "#,
            )
            .unwrap();
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();
        let value = string.parse_object("sleeps").unwrap();
        assert!(
            irtg.parse([string.input(value)])
                .unwrap()
                .automaton
                .viterbi()
                .is_some()
        );
    }

    #[test]
    fn rejects_unknown_tree_and_extra_closing_brace() {
        assert!(TulipacInputCodec.decode("word x: missing").is_err());
        assert!(
            TulipacInputCodec
                .decode("tree t: S { V+ } } word x: t")
                .is_err()
        );
    }

    #[test]
    fn generated_tree_interpretation_is_not_binarized() {
        let irtg = TulipacInputCodec.decode(CHASING).unwrap();
        assert!(irtg.interpretation::<TagTreeAlgebra>("tree").is_ok());
        assert!(
            irtg.interpretation::<Binarizing<TagTreeAlgebra>>("tree")
                .is_err()
        );
    }

    #[test]
    fn feature_filter_enforces_tulipac_agreement() {
        let irtg = TulipacInputCodec
            .decode(
                r#"
                tree noun:
                  S {
                    Det! [gen=?g]
                    N+ [gen=?g]
                  }
                tree det:
                  Det+
                word 'Hund': noun[gen=masc]
                word 'der': det[gen=masc]
                word 'die': det[gen=fem]
                "#,
            )
            .unwrap();
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();

        let good = string.parse_object("der Hund").unwrap();
        let good_chart = irtg.parse([string.input(good)]).unwrap();
        assert!(
            irtg.filter_non_null(&good_chart.automaton, "ft")
                .unwrap()
                .viterbi()
                .is_some()
        );

        let bad = string.parse_object("die Hund").unwrap();
        let bad_chart = irtg.parse([string.input(bad)]).unwrap();
        assert!(bad_chart.automaton.viterbi().is_some());
        assert!(
            irtg.filter_non_null(&bad_chart.automaton, "ft")
                .unwrap()
                .viterbi()
                .is_none()
        );
    }

    #[test]
    fn shieber_subject_adjunction_clashes_and_feature_filter_removes_it() {
        let irtg = TulipacInputCodec.decode(SHIEBER).unwrap();
        let mut language = irtg.grammar().sorted_language();
        let mut successful = 0;
        let mut failed = 0;
        for _ in 0..12 {
            let weighted = language.next().unwrap();
            let (arena, root) = language.clone_tree(weighted.tree());
            if irtg
                .interpretation_ref("ft")
                .unwrap()
                .evaluate_derivation(&arena, root)
                .is_ok()
            {
                successful += 1;
            } else {
                failed += 1;
            }
        }
        assert!(successful > 0);
        assert!(failed > 0);

        let filtered = irtg.filter_non_null(irtg.grammar(), "ft").unwrap();
        let mut filtered_language = filtered.sorted_language();
        for _ in 0..3 {
            let weighted = filtered_language.next().unwrap();
            let (arena, root) = filtered_language.clone_tree(weighted.tree());
            assert!(
                irtg.interpretation_ref("ft")
                    .unwrap()
                    .evaluate_derivation(&arena, root)
                    .is_ok()
            );
        }
    }

    #[test]
    fn read_path_resolves_relative_includes() {
        let directory =
            std::env::temp_dir().join(format!("rusty_alto_tulipac_{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let trees = directory.join("trees.tag");
        let grammar = directory.join("grammar.tag");
        std::fs::write(&trees, "tree v: S @NA { V+ }").unwrap();
        std::fs::write(&grammar, "#include 'trees.tag'\nword sleeps: v").unwrap();

        let stream_error = TulipacInputCodec
            .decode("#include 'trees.tag'\nword sleeps: v")
            .unwrap_err();
        assert!(stream_error.to_string().contains("requires"));

        let registry = crate::InputCodecRegistry::standard();
        let codec = registry.codec_for_path::<Irtg>(&grammar).unwrap();
        let irtg = codec.read_path(&grammar).unwrap();
        let string = irtg.interpretation::<TagStringAlgebra>("string").unwrap();
        let value = string.parse_object("sleeps").unwrap();
        assert!(
            irtg.parse([string.input(value)])
                .unwrap()
                .automaton
                .viterbi()
                .is_some()
        );

        std::fs::remove_dir_all(directory).unwrap();
    }
}
