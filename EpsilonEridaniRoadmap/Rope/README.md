# Ropes

Build a persistent sequence over an arbitrary element type, represented by an
AVL-balanced binary tree with bounded, non-empty list chunks at its leaves.
Indexing, concatenation, and positional splitting are the central operations;
insertion, range erasure, extraction, and replacement are derived from split and
join. Every operation is verified against `List α`.

An editor buffer over `Rope Char` and a persistent event log illustrate the API:
retain old versions, concatenate fragments, and edit or extract by position.
These are illustrations, not downstream application targets. Filling the gap in
the library is sufficient motivation; no downstream consumer is claimed.

**Proposed layout:** `EpsilonEridani/Algorithms/Lean/Rope/` in the
[content repository](https://github.com/cslib-community/EpsilonEridani).
This roadmap follows the accepted [B-tree roadmap](../BTree/README.md) in
separating correctness from cost. Milestones 1–6 establish correctness, without
cost statements. Milestones 7–10 add instrumented instantiations and explicit
bounds to the same definitions. The dependency order is given below.

[`Suggested.lean`](Suggested.lean) illustrates the structure, invariants, key
operations, and theorem shapes. It is not an exhaustive checklist and its
`sorry` bodies are targets, not implementations. This README is the specification.
The choices incorporate the discussion in
[proposal #10](https://github.com/cslib-community/EpsilonEridaniRoadmap/issues/10),
especially [Jesse Alama's review](https://github.com/cslib-community/EpsilonEridaniRoadmap/issues/10#issuecomment-6589992986).

## Existing libraries and prerequisites

The proposal's 2026-10-30 survey found no reusable rope in Lean core, Batteries,
Mathlib, CSLib, complexitylib, or AlgoLib. Jesse confirmed the gap in the pinned
dependencies. The NTP4VC translation of the Why3 proof consists of benchmark proof
obligations; `deepai-org/loom` uses a rope for generated proof artifacts but does
not supply the split, join, balance, and cost theory requested here. Recheck
upstream before implementation rather than treating this survey as permanent.

The package currently pins Epsilon Eridani `14bb994d`, CSLib `1ade21e1`, and
Mathlib `625d8914`, with Lean `v4.36.0-rc1`. The roadmap needs no dependency update.
Use these existing interfaces:

- Lean core's [`List` operations](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Init/Data/List/Basic.lean)
  supply the sequence model, including `insertIdx`, `set`, and `extract`.
- CSLib's [`TimeM`](https://github.com/leanprover/cslib/blob/1ade21e1bd8d03a4ca9f6f632a15c032926054f7/Cslib/Algorithms/Lean/TimeM.lean)
  supplies `ret`, `time`, `tick`, and `isMonadHom_pure_ret`. Its annotations are
  trusted; the charging rules below are part of the specification.
- CSLib's [`IsMonadHom`](https://github.com/leanprover/cslib/blob/1ade21e1bd8d03a4ca9f6f632a15c032926054f7/Cslib/Foundations/Control/Monad/IsMonadHom.lean)
  and [monad-polymorphic merge sort](https://github.com/leanprover/cslib/blob/1ade21e1bd8d03a4ca9f6f632a15c032926054f7/Cslib/Algorithms/Lean/Sort/Merge.lean)
  provide the transfer pattern between instantiations.
- Mathlib's `Nat.fib`, `Nat.log`, and their arithmetic lemmas supply the height
  analysis. Missing inequalities connecting Fibonacci growth to `Nat.log` are
  explicit prerequisites of Milestone 2, to be proved there using those APIs.

No ordered-map implementation supplies positional split and join here.
`Std.TreeMap`, Batteries' red-black trees, the CSLib splay-tree proposal
[leanprover/cslib#568](https://github.com/leanprover/cslib/pull/568), and the B-tree
roadmap are related work, not prerequisites. In particular, B-tree split and join
are out of scope there. Ropes make no element comparisons, so this roadmap does
not require CSLib's comparison-query framework or an order on `α`.

## Conventions

### Representation and invariants

`Rope α` is a plain inductive type with constructors `empty`, `leaf xs`, and
`node cachedLength cachedHeight left right`. There are no proof fields. The
chunk bound `B : ℕ` is a term parameter of the validity predicate and of bulk
construction, not of the type. Theorems involving chunk bounds assume `1 ≤ B`.
The monad-polymorphic executable API fixes `α : Type` and
`m : Type → Type w`, matching `TimeM`'s universe discipline.

There are three independent, decidable predicates, with inversion lemmas:

- `CacheCorrect`: caches are correct recursively. At a node, cached length is
  the sum of child lengths and cached height is one plus their maximum height.
- `Chunked B`: each leaf has between 1 and `B` elements, and both children of
  every internal node are non-empty. The empty rope is the `empty` constructor,
  never `leaf []`. There is no minimum occupancy greater than one.
- `Balanced`: both subtrees are balanced and their structural heights differ
  by at most one.

`IsWF B t` is their conjunction, used as a theorem hypothesis. State lemmas under
only the components they need. A bundled user-facing wrapper may be added after
the raw API, but is not a prerequisite for any milestone.

`length` and `height` read cached fields at internal nodes; a leaf's length is
`xs.length`. Both `empty` and a leaf have height **zero**. An internal node has
structural height `max left.structuralHeight right.structuralHeight + 1`.
`CacheCorrect` relates cached height to structural height. Thus height counts
internal nodes along the longest path, and `empty` and a singleton leaf can have
the same height without being confused. `leaves` counts leaves, not elements.

`toList` enumerates leaves left to right. Its executable conversion uses an
accumulator, not repeated flattening of the left subtree at each node. Supply
constructor equations, cached-field agreement, and `length = toList.length`.
There is no structural extensionality theorem: different valid trees and chunk
boundaries may represent the same list.

### Chunking and balancing

`ofList B` partitions its input into consecutive chunks of size `B`, except for
a possibly shorter final chunk, and builds a balanced tree in bulk. On `[]` it
returns `empty`. Its total definition may use `max 1 B`; the specification and
bounds concern `1 ≤ B`.

`join` (also exposed as `append`) is purely structural: it never merges, splits,
or copies a leaf. Small chunks remain small. `splitAt` may cut one leaf into two
smaller non-empty leaves, using `empty` for an empty result. Only `ofList`
chunks an arbitrary input sequence; it is not a global occupancy invariant.
`compact B t := ofList B (toList t)` restores bulk chunking explicitly.

Follow the AVL join scheme of Blelloch, Ferizovic, and Sun, Section 3 (AVL trees),
Figure 2 and Lemma 1/Theorem 1, adapted to leaf sequences. `balanceNode` is the local single/double
rotation constructor for balanced children whose heights differ by at most two;
it recomputes caches and eliminates empty children. `join` descends the taller
spine until the heights differ by at most one and then uses this same constructor
on the return path. Prove rotation balance preservation once and reuse it.
Unlike the paper's ordered trees, internal nodes carry no key. A two-child node
is enough at the base case; do not use its `join2`/split-last detour.

### Sequence semantics and boundaries

All positions are natural-number **element indices**, starting at zero. For
`Rope Char`, they count `Char` values through `String.toList`, not UTF-8 bytes,
grapheme clusters, or `String.Pos`. With `l := toList t`:

| Operation | Required model equation / convention |
| --- | --- |
| `get? t i` | `l[i]?`; out of range returns `none` |
| `join a b`, `append a b` | `toList a ++ toList b` |
| `splitAt t i` | `(l.take i, l.drop i)`; a large index gives `(l, [])` |
| `insertAt t i x` | `l.insertIdx i x`; `i = l.length` appends, `i > l.length` leaves `l` unchanged |
| `set t i x` | `l.set i x`; out of range leaves `l` unchanged |
| `extract t i j` | `l.extract i j = (l.drop i).take (j - i)` |
| `erase t i j`, when `i ≤ j` | `l.take i ++ l.drop j` |
| `erase t i j`, when `j < i` | `l` (identity) |
| `map f t` | `l.map f` |
| `foldl f z t`, `foldr f z t` | `l.foldl f z`, `l.foldr f z` |
| `x ∈ t` | `x ∈ l` |

Ranges are half-open `[i, j)`. `extract` with reversed endpoints is empty.
Erasure with reversed endpoints is the identity; the `take i ++ drop j` equation
therefore requires `i ≤ j`, since otherwise it can duplicate elements. Endpoints
past the length are handled by core's `take`/`drop` semantics. Guard insertion
and replacement before splitting, to preserve core's out-of-range behavior.

### One operation definition, two stages

From the first executable operation, define it once over a monad, taking
`tick : ℕ → m Unit`. A `TimeM` adapter can discard `tick`'s `PUnit` result.
The pure API is the `Id` instantiation with `tick := fun _ => pure ()`.
Correctness milestones state only model equations, invariant preservation,
and size/height effects about that API; they contain no cost statements.

The cost stage specializes the same definitions at `TimeM ℕ`, proves that `ret`
is the pure result, and proves the bounds. Supply a naturality/transfer lemma for
each operation using `IsMonadHom`, assuming the homomorphism maps one tick action
to the other. Specialize it using `TimeM.isMonadHom_pure_ret`. No algorithm is
rewritten, no second timed algorithm is introduced, and no correctness theorem
is made dependent on a cost theorem.

### Cost model and fixed bounds

Use one natural-number counter:

- Charge one tick on each inspection of an internal node by an operation,
  including nodes inspected to choose a rotation. Repeated inspections by
  distinct primitive calls count again. Cached-field reads alone are free.
- Charge one tick for each element copied into a newly constructed leaf list,
  and into an output list during `toList`. Count actual list-cell copying,
  including an extra pass if the chosen implementation copies twice.
  `ofList` copies each input element once into chunks; `map` copies once.
  Splitting a leaf uses `List.take` and `List.drop`: only `take` copies its
  prefix; `drop` shares its suffix. The copy charge is at most `B`.
- Empty/leaf constructor tests, leaf access itself, leaf indexing, traversals
  that do not copy list cells (including `drop` and folds), cached length/height
  reads, index arithmetic/comparison, node allocation, and reconstruction without
  inspecting more internal nodes are free. User callback work is free. A new
  singleton leaf costs one copy tick. There is no extra leaf-visit tick.

This deliberately measures structural inspections and list copying, not RAM
instructions or machine time. In particular, `get?` is bounded by height even
though indexing a `List` leaf takes machine time. Tick placement is trusted,
just as in the B-tree roadmap and CSLib's `TimeM` docstring.

For `h := t.height`, `n := t.length`, define the following **target upper bounds**
(they are proof obligations, not already proved performance claims):

- `H(n) := 2 * Nat.log 2 (n + 1)` bounds height.
- `D(a,b) := (a - b) + (b - a)` is absolute height difference in naturals.
- `J(a,b) := 8 * (D(a,b) + 1)` bounds join cost for heights `a,b`.
- `S(h,B) := 64 * h + B + 8` bounds split cost.

State each structural-operation bound in height first, and derive the explicit
logarithmic corollary via `h ≤ H(n)`. In particular, split has corollary
`time ≤ 128 * Nat.log 2 (n + 1) + B + 8`. Join's corollary can use
`8 * (max (H(n₁)) (H(n₂)) + 1)`, while retaining the sharper height-difference
theorem as the principal result. Loose constants are intentional, but increasing
them requires a roadmap change with the revised charging argument.

## Stage 1: correctness

### Milestone 1: structure, model, and basic API

Define the tree, cached selectors, structural height and leaf count, the three
predicates, their decidability and inversion/constructor lemmas, and `IsWF`.
Provide `empty`, singleton, `toList`, `length`, `get?`, membership, `map`, both
folds, and chunked `ofList` using the monadic shape above. Give model equations
for each, including `toList_map`, fold equations, `toList_ofList`, length
agreement, and the relevant cache/chunk preservation lemmas. Mapping preserves
shape, height, and balance whenever these held on the input.

Bulk construction's balance proof may wait until Milestone 2. Include small
`decide`/`rfl`-checked examples at `B = 1` and `B = 2`: valid trees, a stale
length cache, a stale height cache, an oversized or empty leaf, an empty internal
child, and an imbalance with otherwise correct caches/chunks. Include boundary
examples from the table using core lists, so they do not rely on unfinished tree
operations. No examples may be discharged with `sorry`.

**Acceptance:** the basic definitions, model and cache/chunk lemmas, predicate
inversion API, and checked examples are present; definitions alone do not finish
this milestone, and no cost theorem is required.

### Milestone 2: local balance and the height bound

Implement `balanceNode` with empty elimination, recomputed caches, and the single
and double rotations, assuming valid balanced children and `D(h₁,h₂) ≤ 2`.
Prove concatenated-list semantics, full well-formedness, and for non-empty inputs
`max h₁ h₂ ≤ height result ≤ max h₁ h₂ + 1`; state the empty cases separately.
Finish balance preservation for `ofList`. Provide the inversion lemmas that
later join proofs need for each rotation case.

Prove `leaves ≤ length`. For a non-empty well-formed tree prove
`Nat.fib (height + 2) ≤ leaves`. The uniform form
`Nat.fib (height + 2) ≤ leaves + 1` also covers `empty`. Derive the explicit
bound `height ≤ 2 * Nat.log 2 (length + 1)`, including `empty` and one-leaf
ropes. Supply the Fibonacci-growth arithmetic needed for this derivation here;
no unnamed constant or deferred complexity prerequisite is allowed.

**Acceptance:** rotations, bulk balance, the Fibonacci lemma, and the stated
height inequality are proved without cost statements.

### Milestone 3: structural join / append

Implement join through Milestone 2's constructor. Prove concatenation semantics,
cache/chunk/balance preservation, empty identities, length addition, preservation
of the concatenated sequence of leaf chunks, and
`max h₁ h₂ ≤ height result ≤ max h₁ h₂ + 1` for non-empty inputs. Empty input
identities have the other tree's height exactly.

Record the spine/height-effect lemmas needed to prove the **height-difference**
cost bound in Milestone 8. A bound proportional to the whole height per join is
insufficient for split: applying it at each ancestor only gives a quadratic
height estimate. The later split analysis must telescope height differences.

**Acceptance:** join and append have their full correctness and height-effect
API, use the shared rotation routine, and leave leaf chunks unchanged; no cost
proof is required yet.

### Milestone 4: positional split

Implement the single-path descent and joins on return, splitting at most one
leaf. Prove the `take`/`drop` pair equations, well-formedness of both outputs,
lengths `min i n` and `n - i`, reconstruction of the original list by append,
and output heights at most the input height. Include `i = 0`, `i = n`, `i > n`,
and cuts inside a chunk and exactly between chunks.

**Acceptance:** both output models, invariant preservation, length and height
effects, and boundary lemmas are proved; no cost theorem is required.

### Milestone 5: derived edits

Define insertion as one split, creation of a singleton, and two joins when
`i ≤ n`, otherwise identity. Define extraction as a split at `i` followed by a
split of the suffix at `j - i`, keeping its prefix. Define erasure by the same
two splits and a join of the retained prefix and suffix when `i ≤ j`, otherwise
identity. Define replacement for `i < n` by splitting at `i`, splitting one
element off the suffix, then joining prefix, new singleton, and remaining suffix;
otherwise identity. Each definition calls the monadic primitives directly.

Prove every table equation, full invariant preservation, and length effects:
insert adds one iff `i ≤ n`; set preserves length; extract has length
`min (j - i) (n - i)`; erase for `i ≤ j` has length
`min i n + (n - j)`. Derive explicit height effects by composition of split/join
lemmas and the output-length height bound, rather than assuming edits preserve
shape. Supply empty, reversed-range, and out-of-range examples/lemmas.

**Acceptance:** all four edits have their model, invariant, length, and height
lemmas, including the guard behavior, with no cost statements.

### Milestone 6: strings and compaction

Define `ofString B s := ofList B s.toList` and
`toString t := String.ofList (toList t)` (`String.mk` in the review is the
deprecated alias in the pinned toolchain). Prove exactly the two sequence round trips:
`toString (ofString B s) = s` and
`toList (ofString B (toString t)) = toList t`. The latter is sequence equality,
not tree equality. Reuse the list-model bridge; develop nothing about `String.Pos`.

Define compaction as `ofList B ∘ toList`. Prove its list equation, well-formedness
for `1 ≤ B`, the bulk chunk-size property (all but the last chunk have size `B`),
and the resulting height bound. Compaction is not a prerequisite for join or edits.

**Acceptance:** the two string round trips and compaction's sequence, chunking,
and balance properties are proved without cost statements.

## Stage 2: costs on the same definitions

### Milestone 7: transfer and basic costs

Add the `TimeM ℕ` instantiations for Milestone 1, with `ret` equal to the pure
operation through monad-homomorphism transfer. Prove `time(get?) ≤ height` and
its corollary `time(get?) ≤ H(n)`. Cached selectors are free. On well-formed trees,
prove `time(toList) ≤ 2*n + 1`, `time(map) ≤ 2*n + 1`, and
`time(foldl), time(foldr) ≤ n`; callback work is excluded. Prove
`time(ofList B l) ≤ 4*l.length + 1` for `1 ≤ B`, using bulk construction rather
than repeatedly joining singleton ropes. List conversions use an accumulator so
that the same elements are not copied at each tree level. Show the internal-node
count is at most the number of non-empty leaves, then use `leaves ≤ n`.

**Acceptance:** all basic timed results transfer to the pure API and meet these
bounds, with no change to Stage 1's algorithm definitions.

### Milestone 8: join and split costs

Add transfer and cost results for `balanceNode`, join, and split. The local
rotation constructor costs at most eight inspections and copies no leaf elements.
Prove `time(join a b) ≤ J(a.height,b.height)`. Prove the height-difference
summation/telescoping lemma along a split path, accounting for rotations as well
as descent, and obtain `time(splitAt t i) ≤ S(h,B)`. Include the single `B`
copying term for the cut leaf, not one `B` per level. Derive the logarithmic
corollaries stated above through the Milestone 2 bound. Do not replace the join
theorem with a whole-height bound or treat the telescoping step as automatic.

**Acceptance:** the height-difference join theorem, telescoping split proof,
and explicit logarithmic corollaries are proved for the unchanged definitions.

### Milestone 9: costs of derived edits

Prove transfer and bounds by adding costs of the actual primitive calls below.
Write `J(p,q)` for `J(p.height,q.height)` and `S(t)` for `S(t.height,B)`.
Intermediate ropes refer to the pure outputs of the corresponding calls:

| Edit branch | Intermediate results | Required bound |
| --- | --- | --- |
| insert, `i ≤ n` | `(p,q) = splitAt t i`, `u = join p (singleton x)` | `S(t) + 1 + J(p,singleton x) + J(u,q)` |
| extract | `(_,q) = splitAt t i` | `S(t) + S(q)` |
| erase, `i ≤ j` | `(p,q) = splitAt t i`, `(_,r) = splitAt q (j-i)` | `S(t) + S(q) + J(p,r)` |
| set, `i < n` | `(p,q) = splitAt t i`, `(_,r) = splitAt q 1`, `u = join p (singleton x)` | `S(t) + S(q) + 1 + J(p,singleton x) + J(u,r)` |

Identity guard branches cost zero. These sums, including the singleton copy,
are the primary bounds; do not hide them in fresh edit-specific constants.
Also give explicit `Nat.log` corollaries by substituting `H` for the heights of
the original and intermediate ropes using their proved length/height effects.
Writing `L := H(n)`, the required corollaries are:

| Edit branch | Logarithmic bound |
| --- | --- |
| insert, `i ≤ n` | `S(L,B) + 1 + 8*(L+1) + 8*(L+2)` |
| extract | `2*S(L,B)` |
| erase, `i ≤ j` | `2*S(L,B) + 8*(L+1)` |
| set, `i < n` | `2*S(L,B) + 1 + 8*(L+1) + 8*(L+2)` |

Split outputs have height at most the original height, and the intermediate
join with a singleton has height at most that height plus one; these facts
justify the substitutions without assuming an intermediate rope has length `n`.

**Acceptance:** every edit has a transfer lemma, the stated primitive-cost sum,
and a logarithmic corollary, without changing its definition.

### Milestone 10: conversion and compaction costs

Transfer the string and compaction operations to `TimeM`. The string bridge
charges the list/rope conversions from Milestone 7; the work performed inside
core's `String.toList` and `String.ofList` is outside this structural cost model.
State this exclusion at the bridge, not as a claim about string runtime.
Compaction has bound `(2*n + 1) + (4*n + 1)` by its two conversions. Prove the
corresponding return-value equations through the existing transfer lemmas.

**Acceptance:** conversion and compaction have the explicit compositional costs
and return-value bridges, without modifying any correctness-stage definition.

## Dependency order and completion

`1 → 2 → 3 → 4 → 5 → 6` is the correctness launch order. Cost work starts after
that stage: `7 → 8 → 9`, with `10` depending on `6` and `7`. No cost milestone
blocks acceptance of a completed correctness milestone. Each milestone requires
its listed lemmas, not just declarations or example computations. A completed
implementation in the content repository has no `sorry`; this roadmap prototype
may retain it. Link implementation PRs to proposal #10 and identify the milestone
being discharged, following the repository's coordination guidance.

## Out of scope

UTF-8 byte positions and encoding proofs; grapheme segmentation; editor-specific
line metadata; gap buffers, piece tables, and mutable storage; lazy/Fibonacci
rebalancing and amortized bounds; concurrency and parallel runtime analysis;
finger trees and arbitrary monoid annotations; machine-time claims; and an editor
or event-log application. Generalizing the AVL machinery to ordered sets or other
sequence structures is possible follow-on work, not a target here. A read-oracle
model showing that structural `get?` reads equal its `TimeM` visit count is another
possible follow-on; there is no optional milestone or query-framework prerequisite.

## References

- Hans-J. Boehm, Russ Atkinson, and Michael Plass, “Ropes: an Alternative to
  Strings”, *Software: Practice and Experience* 25(12), 1315–1330, 1995,
  [doi:10.1002/spe.4380251203](https://doi.org/10.1002/spe.4380251203).
  Historical sequence representation and motivation; its explicit Fibonacci
  rebalancing is not the invariant chosen here.
- Guy E. Blelloch, Daniel Ferizovic, and Yihan Sun, “Just Join for Parallel
  Ordered Sets”, *SPAA* 2016, Section 3 (AVL trees), Figure 2, Lemma 1,
  Theorem 1, and Section 4,
  [author PDF](https://www.cs.cmu.edu/~guyb/papers/BFS16.pdf),
  [doi:10.1145/2935764.2935768](https://doi.org/10.1145/2935764.2935768).
  Source of the AVL spine-join and split analysis, adapted here to leaf sequences.
- Jean-Christophe Filliâtre and Léon Gondelman,
  [Why3 gallery: Ropes](https://toccata.gitlabpages.inria.fr/toccata/gallery/ropes.en.html).
  Prior correctness proof of `get`, concatenation, substring, and explicit
  balancing; useful for model lemmas, not a source of the cost bounds above.
- Nils Anders Danielsson, “Lightweight Semiformal Time Complexity Analysis for
  Purely Functional Data Structures”, *POPL* 2008,
  [doi:10.1145/1328438.1328457](https://doi.org/10.1145/1328438.1328457).
  Background for the annotation-based method used by CSLib's `TimeM`.
