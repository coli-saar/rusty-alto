
Our main design concerns are clean API and efficiency. Prioritize clean abstractions over special-purpose solutions, but feel free to optimize for common use-cases. So special storage for rules of arity <= 2 is fine, but optimization for inverse homomorphism of the string algebra is fishy.

This project is very heavily inspired by Alto, a Java library whose source is in ~/Documents/workspace/alto. Our goal is to read inputs that are compatible with Alto, and to outperform it. We keep code for performance comparisons in tools/alto-compare. Whenever you make tricky algorithm decisions, look to Alto for inspiration while still exploiting performance opportunities that come from Rust and the rest of rusty_alto.

We use rusty-tree as our main tree library. Whenever you generate code for tree handling that is general-purpose enough, make a suggestion to extend rusty-tree rather than adding it to rusty-alto. Do not edit rusty-tree yourself.
