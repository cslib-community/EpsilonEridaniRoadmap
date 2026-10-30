# B-trees

Build B-trees and a small library of theorems about them: the classic B-tree
of Bayer and McCreight with the minimum-degree parametrisation of Cormen,
Leiserson, Rivest and Stein, and the B+-tree layout used by database storage
engines, in which interior nodes hold only separator keys and every entry
lives in a leaf. Both are verified against one specification, the sorted
association list, and both carry worst-case cost bounds in CSLib's `TimeM`
monad with one tick per node visited. The endpoints are the standard map operations, the order queries that
make an ordered map useful, bulk loading, and an output-equality bridge to
Lean's `Std.TreeMap`.

The motivation is storage engines. SQLite's table b-trees keep all data in
leaves and its index b-trees keep keys at every level, which is exactly the
B+-tree and classic pair developed here; [SQLean](https://github.com/cslib-community/sqlean/issues/151)
is an intended consumer of the abstract structure. This roadmap stays at the
level of purely functional trees over an ordered key type. It does not model
pages, bytes, or disks; see [Out of scope](#out-of-scope).

**Suggested homes:** `EpsilonEridani/Algorithms/Lean/BTree/` for both trees,
their operations, and their cost analyses, following the placement of
CSLib's `TimeM` and sorting developments; `EpsilonEridani/Foundations/Data/List/`
for the sorted association list model of Milestone 1.

[`Suggested.lean`](Suggested.lean) provides suggested signatures, never an
exhaustive checklist; this document is the specification.

## Existing libraries and related work

There is no B-tree in CSLib, Lean core, Batteries, or Mathlib. The
developments below supply vocabulary and conventions; the targets are the
missing structures and theory.

- CSLib's [`TimeM`](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/Lean/TimeM.lean)
  is the cost monad. Its ticks are trusted annotations, so the
  [cost model](#cost-model) below fixes what a tick means. CSLib's
  [merge sort](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean)
  shows the house style: a `TimeM` program whose `ret` is proved equal to a
  pure Mathlib function and whose `time` is bounded separately.
- complexitylib's [search-tree cost module](https://github.com/cslib-community/complexitylib/blob/main/Complexity/Algorithms/Lean/SearchTree/Cost.lean)
  fixes the node-visit charging rules adopted here, for unbalanced binary
  search trees over `LinearOrder` keys.
- Lean core's [`Std.TreeMap`](https://github.com/leanprover/lean4/tree/master/src/Std/Data/TreeMap)
  is a weight-balanced binary tree verified through an internal association
  list model. Milestone 5 compares outputs with it; nothing here depends on
  its internals. Core's [`Std.Internal.List.Associative`](https://github.com/leanprover/lean4/blob/master/src/Std/Data/Internal/List/Associative.lean)
  and Batteries'
  [`OrderedAssocList`](https://github.com/leanprover-community/batteries/blob/main/Batteries/Data/OrderedAssocList.lean)
  are prior art for the list model's names and lemma shapes; neither is
  ordered by `LinearOrder`, and the first is an internal namespace, so
  Milestone 1 builds its own.
- Lean core and Mathlib supply `List.Pairwise`, `List.SortedLT`,
  `List.lookup`, `Nat.log`, and the `LinearOrder` API. Use these rather than
  private versions; key-sortedness is `Pairwise (· < ·)` on the key list.

Published formalisations to consult for proof structure, not to port:
Mündler's imperative B-trees and the Mündler–Nipkow B+-trees in Isabelle,
and the Ynot B+-tree of Malecha, Morrisett, Shinnar and Wisnesky in Coq.
Both verify against a sorted-list abstraction; the Isabelle development
separates the functional specification from an imperative refinement in the
way this roadmap separates its trees from a future page-addressed
refinement.

## Conventions and acceptance criteria

### Keys, values, and the model

- Keys have a `LinearOrder`. Values are an arbitrary type. Sets are the
  `Unit`-valued instance and get no separate development.
- A B-tree is a map: inserting an existing key replaces its value. Lookup of
  an absent key returns `none`.
- The specification of every operation is its effect on `toList`, the
  entries in key order. The model is a list of pairs whose keys are strictly
  increasing, so keys are distinct. Model operations are plain list
  functions: lookup agrees with `List.lookup`; insertion, erasure, minimum,
  maximum, predecessor, successor, and closed-interval restriction are
  defined in Milestone 1 and are the reference semantics for every tree
  operation.
- Pure results are extracted with `TimeM.ret`; every operation has a
  `ret_` theorem stating its model equation and a `time_` theorem stating
  its cost bound. Well-formedness is a hypothesis of both, never bundled
  into the tree type.

### Classic B-tree shape

- The minimum degree `t ≥ 2` is a term, not a type-level parameter. A node
  is a first child followed by a list of (key, value, child) triples, so a
  node with `m` keys has `m + 1` children by construction.
- Well-formedness: every node other than the root has between `t - 1` and
  `2t - 1` keys; a non-leaf root has between `1` and `2t - 1` keys; the
  empty tree is the leaf; all leaves are at the same depth; `toList` is
  key-sorted. These are the invariants of Cormen et al., Chapter 18, with
  `t = 2` giving 2-3-4 trees.
- `height` counts nodes on a root-to-leaf path: the leaf has height `0` and
  a node has height one more than the common height of its children.
  `size` is the length of `toList`. The height bound is stated as the
  explicit inequality `height ≤ Nat.log t ((size + 1) / 2) + 1`, together
  with the matching lower bound `2 · t^(height - 1) - 1 ≤ size` for
  non-empty trees and the upper bound `size ≤ (2t)^height - 1`.

### B+-tree shape

- A leaf holds a list of entries; an interior node is a first child followed
  by a list of (separator, child) pairs. Separators are keys, not entries:
  the keys below a separator are strictly smaller than it, and the keys in
  the child it introduces are at least it. A separator need not occur as a
  key in any leaf. Pin this convention; the alternative with separators
  bounding from above is not intended.
- Well-formedness: non-root leaves hold between `t - 1` and `2t - 1`
  entries, non-root interior nodes hold between `t - 1` and `2t - 1`
  separators, a non-leaf root has between `1` and `2t - 1` separators, the
  empty tree is the empty leaf, all leaves are at the same depth, `toList`
  is key-sorted, and the separator convention holds at every interior node.
- `height` counts levels: a leaf has height `1`. The height bound is
  `height ≤ Nat.log t size + 1`.
- Leaf chaining is represented by `leaves`, the list of leaf entry lists in
  key order, with `toList = leaves.flatten`. There are no pointers.

### Cost model

- Costs are `TimeM ℕ`. The tree-level operations charge **one tick per node
  visited**, where a visit is a descent into, or an inspection of, a node
  other than the empty leaf. Following complexitylib's search-tree
  convention, empty-child tests, allocation, reconstruction of nodes on the
  return path, the implementation of key comparison, and client computation
  are not charged. These are node-visit counts, not RAM instruction counts,
  and no machine-time claim is made.
- The within-node search is its own `TimeM` function charging **one tick per
  key comparison**, with its own bound of at most `2t - 1` comparisons per
  node, and the tree-level operations use its pure value. The composed
  comparison bound `(2t - 1) · height` for lookup is a required corollary.
- Bounds are explicit inequalities in `height`, with the `Nat.log` forms
  obtained by composing with the height bound. No big-O statement is a
  target. All bounds are worst-case; no amortised analysis is a target.
- Required bounds: lookup, membership, minimum, maximum, predecessor,
  successor, insertion, and erasure each visit at most `height` nodes.
  Range restriction visits at most `2 · height + k` nodes where `k` is the
  length of its output. Bulk loading of `n` entries builds at most `n`
  nodes. Insertion increases height by at most one; erasure never increases
  it.
- The algorithm shape for insertion and erasure is not prescribed: the
  single-pass top-down algorithms of Cormen et al., with pre-emptive
  splitting and merging, and the bottom-up algorithms of the functional
  literature, in which a recursive call returns either a tree or an
  overflow, both meet the stated bounds. Erasure must handle the interior
  case by replacing with a predecessor or successor entry; silently
  restricting erasure to leaves does not discharge the target.

### API expectations

- Every structure needs the common basic API: `toList`, `size`, `height`,
  `keys`, a `Membership` instance characterised through `toList`, `map`
  over values with `toList_map`, folds characterised through `toList`,
  inversion lemmas for the well-formedness predicate, and `decide`- or
  `rfl`-checked examples at `t = 2` and `t = 3` that distinguish well-formed
  trees from trees violating occupancy, depth, or ordering.
- Every operation needs its model equation, its well-formedness
  preservation, its cost bound, and its effect on `size` and `height`.
- Tree-level lemmas are stated for an arbitrary `t`; no lemma may fix
  `t = 2`.

## Milestones

Dependencies name prerequisite milestones, in addition to existing upstream
APIs. Each milestone can be implemented in smaller contributions along its
listed theorem boundaries.

### M1. Sorted association lists

The model, with no trees. Define key-sortedness as strict sortedness of the
key list, and the model operations: lookup (as `List.lookup`),
insert-or-replace, erase, minimum, maximum, strict predecessor and strict
successor of a key, and restriction to a closed key interval. Prove:

1. Each operation preserves key-sortedness; lookup after insert returns the
   new value at that key and is unchanged elsewhere; lookup after erase is
   `none` at that key and unchanged elsewhere; erase of an absent key is the
   identity.
2. On a sorted list, `lookup k l = some v` iff `(k, v) ∈ l`; membership in
   the interval restriction is membership with the key in the interval; the
   predecessor of `k` is the greatest entry with key below `k` or `none`,
   and dually for the successor; minimum and maximum are the head and last
   entry.
3. Length of insert is the old length or one more, according to whether the
   key was present; length of erase dually; both as equalities.
4. Interval restriction is the sublist of entries with keys in the interval,
   and concatenation lemmas for sorted lists split at a key, which the tree
   proofs use at every node.

Name the model `SortedAssoc` or similar and keep it in the foundations
directory; it is list theory, not tree theory.

### M2. B-tree structure and height

Dependencies: M1.

Define the interleaved inductive type, `toList`, `size`, `height`, `keys`,
`map`, folds, membership, the occupancy predicate for non-root nodes, the
equal-depth predicate, and the well-formedness predicate `IsWF t` combining
them with root occupancy and sortedness of `toList`. Prove the basic API of
the [API expectations](#api-expectations), the inversion lemmas (a
well-formed node's children are occupied and equal in height, and every
subtree of a well-formed tree satisfies occupancy), and the three size and
height inequalities of the [classic shape](#classic-b-tree-shape).

### M3. Search and order queries

Dependencies: M2.

Define the within-node search returning the position of the first key not
below the query, charging one tick per comparison, and prove its pure value
and its `2t - 1` bound. Define `lookup`, `contains`, `min?`, `max?`,
`pred?`, `succ?`, and `range lo hi` as `TimeM` programs charging one tick
per node visited and using the pure within-node position. Prove each
operation's model equation on well-formed trees, the `height` bounds of the
[cost model](#cost-model), their `Nat.log` corollaries, and the composed
comparison bound for lookup.

### M4. Insertion and erasure

Dependencies: M3.

Define `insert k v` and `erase k` as `TimeM` programs. Prove on well-formed
trees: the model equations with M1's insert-or-replace and erase; preservation
of `IsWF t`; the node-visit bounds; the height and size effects. Derive
`eraseMin?` and `eraseMax?` with their model equations and bounds. Include
examples showing a root split at `t = 2` and a root collapse on erasure.

### M5. Bulk loading and the tree-map bridge

Dependencies: M4.

Define `ofSortedList t l` building a well-formed tree from a sorted list in
one pass, with a `TimeM` version charging one tick per node built. Prove
`toList (ofSortedList t l) = l`, well-formedness for `t ≥ 2`, the bound of at
most `l.length` nodes built, and that the result's height meets the height
bound. Prove the bridge: for a sorted list `l`, the `toList` of
`ofSortedList t l` equals the `toList` of `Std.TreeMap.ofList l compare`,
using the `Ord` instance derived from `LinearOrder`. The bridge is an
output equality; no lemma about `Std.TreeMap` internals is a target.

### M6. B+-tree structure and queries

Dependencies: M3, M5.

Define the two-constructor B+-tree type, `toList`, `leaves`, `size`,
`height`, `keys`, `map`, folds, membership, the leaf and interior occupancy
predicates, the equal-depth predicate, the separator predicate, and
`IsWF t`. Prove the basic API, the inversion lemmas, `toList = leaves.flatten`,
and the height bound `height ≤ Nat.log t size + 1` with its lower bound
`t^(height - 1) ≤ size` for trees of height at least two. Define the
within-node separator search, `lookup`, `contains`, `min?`, `max?`,
`pred?`, `succ?`, and `range`, charging as in the classic tree, and prove
the model equations and bounds of M3 for the B+-tree. Range restriction
additionally satisfies: its output is the flattening of a contiguous
sublist of `leaves`, with the first and last leaf restricted.

### M7. B+-tree updates and bulk loading

Dependencies: M4, M6.

Define `insert`, `erase`, `eraseMin?`, `eraseMax?`, and `ofSortedList` for
the B+-tree and prove the statements of M4 and M5 for it, including a bridge
to `Std.TreeMap` and the statement that a B+-tree and a classic B-tree built
from the same sorted list have the same `toList`. Erasure keeps separators
valid without requiring them to be present as keys; include an example in
which an erased key remains as a separator.

## Out of scope

The following are not targets of this roadmap. A reader who needs one of
them should write a roadmap for it, citing this one.

- Page-addressed or arena storage, node identifiers, and any on-disk or
  byte-level format, including SQLite's cell, record, and overflow-page
  layouts.
- `split` at a key and `join` of two trees around a key, and the set
  operations built on them.
- Concurrency, persistence, journaling, and crash safety.
- Amortised analysis, RAM or Turing-machine time bounds, and big-O
  statements.
- Red-black, weight-balanced, AVL, splay, and B*-trees, fractional
  cascading, and any theory of `Std.TreeMap` beyond the output equality of
  M5 and M7.
- Bridges to complexitylib's stateful ordered-set calculus.

## Dependency and launch order

An order satisfying all dependencies is M1, M2, M3, M4, M5, M6, M7. M1 and M2
are each a single self-contained contribution and are the right places to
start. M6 can begin once M3 is merged, in parallel with M4 and M5, except
for its bulk-loading comparison, which waits for M5.

Completion means the structures, operations, model equations, and cost
bounds above are implemented against the existing APIs. Definitions without
their lemmas, or operations without their bounds, do not discharge a
milestone.

## References

These specify the structures and conventions. They do not prescribe a port
of any existing formalisation.

- **Origin:** [Bayer and McCreight, *Organization and maintenance of large
  ordered indexes*, Acta Informatica 1 (1972), 173–189](https://doi.org/10.1007/BF00288683).
- **Survey and the B+-tree:** [Comer, *The Ubiquitous B-Tree*, ACM Computing
  Surveys 11 (1979), 121–137](https://doi.org/10.1145/356770.356776).
- **Minimum-degree conventions and algorithms:** Cormen, Leiserson, Rivest
  and Stein, *Introduction to Algorithms*, Chapter 18; Knuth, *The Art of
  Computer Programming*, Volume 3, Section 6.2.4.
- **Formalisations:** [Mündler, *A Verified Imperative Implementation of
  B-Trees*, Archive of Formal Proofs (2021)](https://www.isa-afp.org/entries/BTree.html);
  [Mündler and Nipkow, *A Verified Implementation of B+-Trees in
  Isabelle/HOL*, ICTAC 2022](https://arxiv.org/abs/2208.09066);
  [Malecha, Morrisett, Shinnar and Wisnesky, *Toward a verified relational
  database management system*, POPL 2010](https://doi.org/10.1145/1706299.1706329).
- **Deployed example:** [SQLite file format, Section 1.6, B-tree
  pages](https://www.sqlite.org/fileformat2.html#b_tree_pages).
