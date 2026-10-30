# B-trees

Build B-trees and a small library of theorems about them: the classic B-tree
of Bayer and McCreight with the minimum-degree parametrisation of Cormen,
Leiserson, Rivest and Stein, and the B+-tree layout used by database storage
engines, in which interior nodes hold only separator keys and every entry
lives in a leaf. Both are verified against one specification, the sorted
association list. Every operation is written once, polymorphically in the
comparator and in a node-visit action, so that it can be run pure, in
CSLib's `TimeM` monad with one tick per node visited, and in CSLib's
query-complexity framework with one query per key comparison. The work is
staged: a correctness stage that delivers the verified classic tree with no
cost statement, a cost stage that adds the node-visit and comparison bounds
together with a comparison lower bound for search, an in-node search that
meets it, and a read-only node-access model in which node visits are
counted structurally, and a B+-tree stage that repeats both for the leaf
layout. An output-equality bridge to Lean's `Std.TreeMap` closes each
bulk-loading milestone.

The motivation is storage engines. SQLite's table b-trees keep all data in
leaves and its index b-trees keep keys at every level, which is exactly the
B+-tree and classic pair developed here; [SQLean](https://github.com/cslib-community/sqlean/issues/151)
is an intended consumer of the abstract structure. This roadmap stays at the
level of purely functional trees over an ordered key type. It does not model
pages, bytes, or disks; see [Out of scope](#out-of-scope).

**Suggested homes:** `EpsilonEridani/Algorithms/Lean/BTree/` for both trees,
their operations, and their cost analyses, following the placement of
CSLib's `TimeM`, `Query`, and sorting developments;
`EpsilonEridani/Foundations/Data/List/` for the sorted association list model
of Milestone 1.

[`Suggested.lean`](Suggested.lean) provides suggested signatures, never an
exhaustive checklist; this document is the specification.

## Existing libraries and related work

There is no B-tree in CSLib, Lean core, Batteries, or Mathlib. The
developments below supply vocabulary and conventions; the targets are the
missing structures and theory.

- CSLib's [`TimeM`](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/Lean/TimeM.lean)
  is the annotation-based cost monad. Its ticks are trusted, so the
  [cost model](#cost-model) below fixes what a tick means.
- CSLib's [query-complexity framework](https://github.com/leanprover/cslib/tree/main/Cslib/Algorithms/Lean/Query)
  represents a program as `FreeM Q α` over a query type `Q`, and derives
  `eval`, `countQueries`, and `cost` from the free monad. Counting is
  structural: only lifted queries are charged, and a program parametric in
  the oracle cannot avoid them. `Cslib.Query.UpperBound` and `LowerBound`
  state bounds over all oracles, `LEQuery` is the comparison query, and
  `FreeM.exists_countQueries_ge_clog` is the adversary lemma giving
  `⌈log_r n⌉` lower bounds. `FreeM.cost` interprets a query program into
  `TimeM`, so the two instrumentations used here already compose. Its
  sorting examples fix the house pattern: define an operation once,
  polymorphically in a monadic comparator, run it pure through `Id`, and
  instantiate it at `TimeM` and at `FreeM (LEQuery α)`, with the
  instantiations related by `IsMonadHom`.
- CSLib's [monad-polymorphic sorts](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/Lean/Sort/Merge.lean)
  and `IsMonadHom` are the mechanism for transferring results between
  instantiations.
- complexitylib's [search-tree cost module](https://github.com/cslib-community/complexitylib/blob/main/Complexity/Algorithms/Lean/SearchTree/Cost.lean)
  fixes the node-visit charging rules adopted here, for unbalanced binary
  search trees over `LinearOrder` keys.
- Lean core's [`Std.TreeMap`](https://github.com/leanprover/lean4/tree/master/src/Std/Data/TreeMap)
  is a weight-balanced binary tree verified through an internal association
  list model. Milestone 5 compares outputs with it; nothing here depends on
  its internals. Core's [`Std.Internal.List.Associative`](https://github.com/leanprover/lean4/blob/master/src/Std/Data/Internal/List/Associative.lean)
  and Batteries'
  [`OrderedAssocList`](https://github.com/leanprover-community/batteries/blob/main/Batteries/Data/OrderedAssocList.lean)
  are prior art for the list model's names and lemma shapes. The Batteries
  list is ordered by a comparator, which `LinearOrder` supplies, and it
  landed on Batteries `main` on 2026-10-25, after the revision this
  roadmap's dependency chain currently pins. Milestone 1 nonetheless builds
  its model as a plain `List (α × β)` with a sortedness predicate: the tree
  proofs need splitting and concatenation lemmas on the entry list at every
  node far more than they need a map container, and that is what the model
  provides. Use the Batteries names where they fit, and bridge to its
  structure if a consumer wants one.
- Lean core and Mathlib supply `List.Pairwise`, `List.SortedLT`,
  `List.lookup`, `Nat.log`, `Nat.clog`, and the `LinearOrder` API. Use these
  rather than private versions; key-sortedness is `Pairwise (· < ·)` on the
  key list.

Published formalisations to consult for proof structure, not to port:
Mündler's imperative B-trees and the Mündler–Nipkow B+-trees in Isabelle,
and the Ynot B+-tree of Malecha, Morrisett, Shinnar and Wisnesky in Coq.
Both verify against a sorted-list abstraction; the Isabelle development
separates the functional specification from an imperative refinement in the
way this roadmap separates its trees from a page-addressed refinement.

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
- Well-formedness is a hypothesis of every theorem, never bundled into the
  tree type.

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
  non-empty trees and the upper bound `size ≤ (2t)^height - 1`. These are
  structural facts about the data structure and belong to the correctness
  stage.

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

### One definition, three instantiations

- Each operation is defined once over an arbitrary monad, taking a
  comparator `le : α → α → m Bool` and a node-visit action `visit : m Unit`,
  with no order instance in scope, so every comparison goes through `le`.
  This shape is fixed from the first operation of Milestone 3; retrofitting
  it later is the expensive part, and the definition itself costs nothing.
- The **pure operation** is the `Id` instantiation with the decidable
  comparator of the order and `visit := pure ()`, as in CSLib's
  `idRun_mergeSortM`. The correctness stage states every model equation,
  well-formedness preservation, and size and height effect about the pure
  operation and never mentions a cost.
- The **node-visit instantiation** is at `TimeM ℕ` with the pure comparator
  and `visit := tick 1`. Its `ret` is the pure operation, proved once
  through `IsMonadHom`.
- The **comparison instantiation** is at `FreeM (LEQuery α)` with
  `LEQuery.ask` and a trivial `visit`. Its `eval` at the oracle of `≤` is
  the pure operation, again through `IsMonadHom`.
- The cost stage adds the two instrumented instantiations, their transfer
  lemmas, and their bounds, to operations whose correctness is already
  established. Nothing in the correctness stage depends on `TimeM` or on
  the query framework.

### Cost model

- **Node visits are the primary model.** One tick per node visited, where a
  visit is a descent into, or an inspection of, a node other than the empty
  leaf. Following complexitylib's search-tree convention, empty-child tests,
  allocation, reconstruction of nodes on the return path, the implementation
  of key comparison, and client computation are not charged. These are
  node-visit counts, not RAM instruction counts, and no machine-time claim
  is made. Tick placement is trusted; Milestone 8 makes the count structural
  for the read-only operations.
- **Comparisons are counted structurally** and stated with
  `Cslib.Query.UpperBound`, quantified over all oracles, with the size
  function being the tree's height on well-formed inputs. The within-node
  search is a comparator-polymorphic function with its own bound. Two
  versions are targets: linear search, at most `2t` comparisons per node,
  and binary search, at most `⌈log₂(2t)⌉ + 1` comparisons per node. The
  binary search's comparison bound holds for every list; its agreement with
  linear search holds for sorted keys, which is the only case the tree
  needs. In-node search runs over a list, so binary search reduces
  comparisons and nothing else; no traversal cost is charged in either
  model, and no claim about it is made.
- **A bound over all oracles must not mention the real order.** Range
  restriction's comparison bound is output-sensitive, and the output under
  an arbitrary oracle is not the output under `≤`, so that bound is stated
  under the oracle of the real order only. The bounds that do not depend on
  the output are stated over all oracles.
- **Lower bounds** come from the framework's adversary lemma. Any
  comparison-based program that computes the rank of a key among `n` keys,
  correctly under every linear order, makes at least `⌈log₂(n + 1)⌉`
  comparisons on some input. The same argument, with its own family of
  inputs, gives the same bound for lookup, whose `n + 1` distinguishable
  answers are the `n` present values and absence. Constructing these
  families is the substance of the lower-bound targets; the lemma supplies
  only the counting. The comparison between upper and lower bounds is stated
  with its dependence on `t` explicit: through the height bound, binary
  in-node search gives at most `(⌈log₂(2t)⌉ + 1) · (log_t ((n + 1) / 2) + 1)`
  comparisons and linear search at most `2t · (log_t ((n + 1) / 2) + 1)`.
  Both are within a constant factor of the lower bound for fixed `t`; the
  constant is bounded for binary search and grows like `t / log t` for
  linear search. The target is the pair of explicit inequalities, not a
  claim that one search is optimal and the other is not.
- Bounds are explicit inequalities in `height`, with the `Nat.log` forms
  obtained by composing with the height bound. No big-O statement is a
  target. All bounds are worst-case; no amortised analysis is a target.
- Required node-visit bounds: lookup, membership, minimum, maximum,
  predecessor, successor, and insertion each visit at most `height` nodes.
  Erasure visits at most `c · height` nodes for a constant `c` fixed by the
  chosen algorithm: borrowing from and merging with siblings inspects nodes
  off the descent path, and under the charging rules above those
  inspections count. The prototype states `3 · height`, which the top-down
  algorithm of Cormen et al. meets by inspecting at most one child and two
  siblings per level; a different algorithm may state a different constant
  with its justification. Range restriction visits at most
  `2 · height + k` nodes where `k` is the length of its output. Bulk loading
  of `n` entries builds at most `n` nodes. Insertion increases height by at
  most one; erasure never increases it. Required comparison bounds are the
  node-visit bounds multiplied by the per-node bound of the in-node search
  in use.
- The algorithm shape for insertion and erasure is not prescribed: the
  single-pass top-down algorithms of Cormen et al., with pre-emptive
  splitting and merging, and the bottom-up algorithms of the functional
  literature, in which a recursive call returns either a tree or an
  overflow, both meet the stated insertion bound, and each meets the
  erasure bound with its own constant. Erasure must handle the interior
  case by replacing with a predecessor or successor entry; silently
  restricting erasure to leaves does not discharge the target.

### API expectations

- Every structure needs the common basic API: `toList`, `size`, `height`,
  `keys`, a `Membership` instance characterised through `toList`, `map`
  over values with `toList_map`, folds characterised through `toList`,
  inversion lemmas for the well-formedness predicate, and `decide`- or
  `rfl`-checked examples at `t = 2` and `t = 3` that distinguish well-formed
  trees from trees violating occupancy, depth, or ordering.
- In the correctness stage, every operation needs its monad-polymorphic
  definition, its pure instantiation, its model equation, its
  well-formedness preservation, and its effect on `size` and `height`.
- In the cost stage, every operation needs its `TimeM` and `FreeM`
  instantiations, the two transfer lemmas, and both cost bounds.
- Acceptance is per milestone. A correctness milestone is complete with no
  cost statement, and a cost milestone is complete without touching the
  operations' definitions.
- Tree-level lemmas are stated for an arbitrary `t`; no lemma may fix
  `t = 2`.

## Milestones

Dependencies name prerequisite milestones, in addition to existing upstream
APIs. Each milestone can be implemented in smaller contributions along its
listed theorem boundaries.

### Stage 1: the classic B-tree, verified

#### M1. Sorted association lists

The model, with no trees. Define key-sortedness as strict sortedness of the
key list, and the model operations: lookup (as `List.lookup`),
insert-or-replace, erase, minimum, maximum, strict predecessor and strict
successor of a key, restriction to a closed key interval, and the rank of a
key, the number of keys strictly below it. Prove:

1. Each operation preserves key-sortedness; lookup after insert returns the
   new value at that key and is unchanged elsewhere; lookup after erase is
   `none` at that key and unchanged elsewhere; erase of an absent key is the
   identity.
2. On a sorted list, `lookup k l = some v` iff `(k, v) ∈ l`; membership in
   the interval restriction is membership with the key in the interval; the
   predecessor of `k` is the greatest entry with key below `k` or `none`,
   and dually for the successor; minimum and maximum are the head and last
   entry; the rank of `k` is the length of the prefix of keys below `k`.
3. Length of insert is the old length or one more, according to whether the
   key was present; length of erase dually; both as equalities.
4. Interval restriction is the sublist of entries with keys in the interval,
   and concatenation lemmas for sorted lists split at a key, which the tree
   proofs use at every node.

Name the model `SortedAssoc` or similar and keep it in the foundations
directory; it is list theory, not tree theory.

#### M2. B-tree structure and height

Dependencies: M1.

Define the interleaved inductive type, `toList`, `size`, `height`, `keys`,
`map`, folds, membership, the occupancy predicate for non-root nodes, the
equal-depth predicate, and the well-formedness predicate `IsWF t` combining
them with root occupancy and sortedness of `toList`. Prove the basic API of
the [API expectations](#api-expectations), the inversion lemmas (a
well-formed node's children are occupied and equal in height, and every
subtree of a well-formed tree satisfies occupancy), and the three size and
height inequalities of the [classic shape](#classic-b-tree-shape).

#### M3. Search and order queries

Dependencies: M2.

Define the comparator-polymorphic within-node linear search, returning the
position of the first key not below the query, and prove its pure value is
the length of the prefix of keys below the query. Define `lookupM`,
`containsM`, `minM`, `maxM`, `predM`, `succM`, `rangeM`, and `rankM`
polymorphically in the comparator and the visit action, and their pure
instantiations `lookup`, `contains`, `min?`, `max?`, `pred?`, `succ?`,
`range`, and `rank`. Prove each operation's model equation on well-formed
trees. No cost statement is a target here.

#### M4. Insertion and erasure

Dependencies: M3.

Define `insertM` and `eraseM` polymorphically, with their pure
instantiations. Prove on well-formed trees: the model equations with M1's
insert-or-replace and erase; preservation of `IsWF t`; the height and size
effects, including that insertion raises the height by at most one and
erasure never raises it. Derive `eraseMin?` and `eraseMax?` with their model
equations. Include examples showing a root split at `t = 2` and a root
collapse on erasure.

#### M5. Bulk loading and the tree-map bridge

Dependencies: M4.

Define `ofSortedList t l` building a well-formed tree from a sorted list in
one pass. Prove `toList (ofSortedList t l) = l`, well-formedness for
`t ≥ 2`, and that the result's height meets the height bound. Prove the
bridge: for a sorted list `l`, the `toList` of `ofSortedList t l` equals the
`toList` of `Std.TreeMap.ofList l compare`, using the `Ord` instance derived
from `LinearOrder`. The bridge is an output equality; no lemma about
`Std.TreeMap` internals is a target.

Stage 1 ends here. A contributor who stops at M5 has delivered a verified
B-tree.

### Stage 2: costs

#### M6. Node-visit bounds

Dependencies: M5.

Instantiate every operation of M3, M4, and M5 at `TimeM ℕ` with one tick
per node visited, and `ofSortedList` with one tick per node built. Prove
the transfer lemma that each instantiation's `ret` is the pure operation,
once through `IsMonadHom`. Prove the node-visit bounds of the
[cost model](#cost-model): `height` for the point queries and insertion,
`c · height` for erasure with the constant stated and justified, and the
output-sensitive bound for range restriction; `n` nodes for bulk loading;
and the `Nat.log` corollaries through the height bound.

#### M7. Comparison bounds and the search lower bound

Dependencies: M4, M5.

Instantiate the operations of M3 and M4 at `FreeM (LEQuery α)` and prove the
transfer lemma from `eval` at the order's oracle to the pure operation.
Prove the comparison `UpperBound` statements over all oracles with linear
in-node search, and the output-sensitive bound for range restriction under
the real order. Define the within-node binary search, prove its comparison
bound for every list and its agreement with linear search on sorted keys,
define lookup and rank with binary in-node search, and prove their
`UpperBound` statements.

Define the correctness predicates for comparison-based rank and lookup
programs, correct under every linear order on the key type, and prove the
`⌈log₂(n + 1)⌉` comparison lower bound for each on an infinite key type,
using `FreeM.exists_countQueries_ge_clog` with an explicit family of
`n + 1` inputs with distinct answers. Prove that the B-tree rank and lookup
programs on a bulk-loaded tree satisfy the predicates, and record the
explicit upper bounds in `n` for both in-node searches through the height
bound, as the [cost model](#cost-model) states them.

#### M8. Read-only operations behind a node-access oracle

Dependencies: M3, M6.

Make the node-visit count structural for the read-only operations. Define
a node-access query type whose single query reads the contents of a node
behind an abstract handle: a first child reference and the (key, value,
child reference) triples, where a reference is an `Option` of a handle and
`none` is the empty leaf. A store is a function from handles to node
contents and is the oracle. Define, by recursion on the functional tree,
the relation that a reference in a store denotes a given tree. Write
`lookupR`, `minR`, `maxR`, `predR`, `succR`, and `rangeR` as `FreeM`
programs over the node-access query, parametric in the handle type so the
tree is visible only through reads, with a fuel argument bounding the
descent. Prove, when the reference denotes a well-formed tree and the fuel
is at least its height: `eval` at the store's oracle equals the pure
operation, and `countQueries` equals the `TimeM` instantiation's visit
count, hence is at most `height` for the point queries and at most
`2 · height + k` for range restriction. Making the empty leaf visible as
`none` is what lets reads equal visits exactly: the empty tree is read
zero times, as it is visited zero times. Updates are not targets here; the
framework's oracles are stateless.

### Stage 3: B+-trees

#### M9. B+-tree structure and queries

Dependencies: M3, M5.

Define the two-constructor B+-tree type, `toList`, `leaves`, `size`,
`height`, `keys`, `map`, folds, membership, the leaf and interior occupancy
predicates, the equal-depth predicate, the separator predicate, and
`IsWF t`. Prove the basic API, the inversion lemmas, `toList = leaves.flatten`,
and the height bound `height ≤ Nat.log t size + 1` with its lower bound
`t^(height - 1) ≤ size` for trees of height at least two. Define the
within-node separator search and the read operations of M3, polymorphic
with pure instantiations, and prove the model equations. Range restriction
additionally satisfies: `leaves` splits as a prefix, a contiguous run, and
a suffix, the output is the run's restriction, every leaf of the run
contributes at least one entry, and every leaf of the run other than its
first and last is returned whole.

#### M10. B+-tree updates and bulk loading

Dependencies: M4, M9.

Define `insertM`, `eraseM`, `eraseMin?`, `eraseMax?`, and `ofSortedList` for
the B+-tree and prove the correctness statements of M4 and M5 for it,
including a bridge to `Std.TreeMap` and the statement that a B+-tree and a
classic B-tree built from the same sorted list have the same `toList`.
Erasure keeps separators valid without requiring them to be present as
keys; include an example in which an erased key remains as a separator.

#### M11. B+-tree cost bounds

Dependencies: M6, M7, M10.

Instantiate the B+-tree operations at `TimeM ℕ` and at `FreeM (LEQuery α)`,
prove the transfer lemmas, and prove the node-visit and comparison bounds of
M6 and M7 for them, with the erasure constant stated for the chosen
algorithm.

## Out of scope

The following are not targets of this roadmap. A reader who needs one of
them should write a roadmap for it, citing this one.

- Page-addressed or arena storage as a data structure with its own
  operations, node allocation, and any on-disk or byte-level format,
  including SQLite's cell, record, and overflow-page layouts. M8's store is
  an oracle for reading, not a structure that is updated.
- Updates through a stateful oracle, and any extension of the query
  framework to stateful queries.
- `split` at a key and `join` of two trees around a key, and the set
  operations built on them.
- Concurrency, persistence, journaling, and crash safety.
- Amortised analysis, RAM or Turing-machine time bounds, and big-O
  statements.
- Red-black, weight-balanced, AVL, splay, and B*-trees, fractional
  cascading, and any theory of `Std.TreeMap` beyond the output equality of
  M5 and M10.
- Bridges to complexitylib's stateful ordered-set calculus.

## Dependency and launch order

An order satisfying all dependencies is M1 through M11 in sequence. M1 and
M2 are each a single self-contained contribution and are the right places to
start. After M5, three lines open in parallel: M6 then M8, M7, and M9 then
M10. M11 waits for all three.

A Stage 1 milestone is complete when its definitions, model equations,
well-formedness preservation, and size and height effects are implemented
against the existing APIs. A Stage 2 or Stage 3 cost milestone is complete
when its instantiations, transfer lemmas, and bounds are. Definitions
without their lemmas do not discharge a milestone.

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
- **Query complexity:** CSLib's
  [query framework](https://github.com/leanprover/cslib/pull/401) and its
  module documentation; the adversary argument is the standard
  decision-tree lower bound of Knuth, Volume 3, Section 6.2.1.
- **Formalisations:** [Mündler, *A Verified Imperative Implementation of
  B-Trees*, Archive of Formal Proofs (2021)](https://www.isa-afp.org/entries/BTree.html);
  [Mündler and Nipkow, *A Verified Implementation of B+-Trees in
  Isabelle/HOL*, ICTAC 2022](https://arxiv.org/abs/2208.09066);
  [Malecha, Morrisett, Shinnar and Wisnesky, *Toward a verified relational
  database management system*, POPL 2010](https://doi.org/10.1145/1706299.1706329).
- **Deployed example:** [SQLite file format, Section 1.6, B-tree
  pages](https://www.sqlite.org/fileformat2.html#b_tree_pages).
