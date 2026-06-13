# Tree Integration Notes

rusty-tree's `TreeArena<E>` now has `len()`, `is_empty()`, `post_order()`, `copy_into()`, and `dup_subtree()`. This makes it straightforward to bridge `TreeArena` with rusty-alto's `Arena` trait and to clean up a manual reimplementation.

## 1. `Tree` as `NodeId`

`Tree` already satisfies the `NodeId` contract: it's `Copy + Eq + Hash` and has `fn index(self) -> usize`. One impl in `src/arena.rs`:

```rust
impl crate::NodeId for rusty_tree::tree::Tree {
    fn index(self) -> usize {
        self.index()
    }
}
```

## 2. `Arena` for `TreeArena<Symbol>`

With `len()` and `post_order()` now available, the impl is mechanical. Add to `src/arena.rs`:

```rust
impl crate::Arena for rusty_tree::tree::TreeArena<crate::Symbol> {
    type NodeId = rusty_tree::tree::Tree;
    type Children<'a> = std::iter::Copied<std::slice::Iter<'a, rusty_tree::tree::Tree>>;
    type PostOrder<'a> = std::vec::IntoIter<rusty_tree::tree::Tree>;

    fn len(&self) -> usize {
        self.len()
    }

    fn symbol(&self, n: Self::NodeId) -> crate::Symbol {
        *self.get_label(n)
    }

    fn children(&self, n: Self::NodeId) -> Self::Children<'_> {
        self.get_children(n).iter().copied()
    }

    fn post_order(&self, root: Self::NodeId) -> Self::PostOrder<'_> {
        // collect to satisfy the concrete associated type requirement
        self.post_order(root).collect::<Vec<_>>().into_iter()
    }
}
```

This lets `TreeArena<Symbol>` trees be passed directly to `run_det` and `run_nondet` without wrapping in `TestArena`.

## 3. Replace `clone_tree` in `sorted_language.rs`

The manual `copy_rec` helper (lines 96–111) reimplements `copy_into`. Replace:

```rust
// Before
pub fn clone_tree(&self, root: Tree) -> (TreeArena<Symbol>, Tree) {
    fn copy_rec(source: &TreeArena<Symbol>, target: &mut TreeArena<Symbol>, root: Tree) -> Tree {
        let children = source.get_children(root).iter()
            .map(|&child| copy_rec(source, target, child))
            .collect();
        target.add_node(*source.get_label(root), children)
    }
    let mut target = TreeArena::new();
    let root = copy_rec(&self.arena, &mut target, root);
    (target, root)
}

// After
pub fn clone_tree(&self, root: Tree) -> (TreeArena<Symbol>, Tree) {
    let mut target = TreeArena::new();
    let root = self.arena.copy_into(root, &mut target);
    (target, root)
}
```
