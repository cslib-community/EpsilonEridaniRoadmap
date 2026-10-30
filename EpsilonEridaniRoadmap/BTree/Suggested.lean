module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Log
public import Std.Data.TreeMap
public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# B-trees: suggested signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is `README.md`.
The declarations below suggest Lean forms for the load-bearing structures and a few milestone
statements, so that contributors and reviewers converge on names and shapes. Discharging every
declaration here finishes neither a milestone nor the roadmap. `sorry` is allowed in this
human-owned roadmap library: these are targets, not completed definitions or proofs.

The pinned choices illustrated here are:

- Keys carry a `LinearOrder`; values are arbitrary. Trees are maps, and insertion replaces.
- The specification of every operation is its effect on `toList`, compared with the sorted
  association list model of Milestone 1.
- A classic node is a first child followed by `(key, value, child)` triples, so a node with `m`
  keys has `m + 1` children by construction. A B+-tree leaf holds entries; an interior node is a
  first child followed by `(separator, child)` pairs.
- Well-formedness is a predicate carried as a hypothesis, never bundled into the type. The
  minimum degree `t` is a term.
- Each operation is defined once over an arbitrary monad, taking a comparator `le` and a
  node-visit action `visit`, with no order instance in scope. The pure operation is its `Id`
  instantiation; the correctness stage (Milestones 1 to 5) speaks only about that. The cost
  stage instantiates it at `TimeM ℕ` (one tick per node visited, the primary model) and at
  `FreeM (LEQuery α)` (one query per comparison, counted structurally and stated with
  `Cslib.Query.UpperBound`), with transfer lemmas back to the pure operation.
- Bounds are explicit inequalities in `height`, with `Nat.log` corollaries. No big-O.
- The comparator-polymorphic sections fix the key and value types in `Type`, as CSLib's
  comparison queries do; the tree type itself is universe-polymorphic.

Milestones 1 to 8 are prototyped in detail; Milestones 9 to 11 give headline signatures only.
-/

namespace EpsilonEridani

open Cslib (FreeM)
open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM
open Cslib.Query (LEQuery UpperBound LowerBound)

universe u v w

/-! # Stage 1: the classic B-tree, verified -/

/-! ## Milestone 1: sorted association lists -/

namespace SortedAssoc

variable {α : Type u} {β : Type v} [LinearOrder α]

/-- Keys strictly increasing, hence distinct. -/
def IsSortedAssoc (l : List (α × β)) : Prop :=
  (l.map Prod.fst).Pairwise (· < ·)

/-- Lookup is `List.lookup`; the model does not introduce a second lookup. -/
abbrev lookup (k : α) (l : List (α × β)) : Option β :=
  List.lookup k l

/-- Insert-or-replace at the sorted position. -/
def insert (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k = k' then (k, v) :: rest
    else (k', v') :: insert k v rest

/-- Remove the entry with key `k`, if any. -/
def erase (k : α) (l : List (α × β)) : List (α × β) :=
  l.filter fun p => p.1 ≠ k

/-- The entry with least key. -/
abbrev min? (l : List (α × β)) : Option (α × β) := l.head?

/-- The entry with greatest key. -/
abbrev max? (l : List (α × β)) : Option (α × β) := l.getLast?

/-- The greatest entry with key strictly below `k`. -/
def pred? (k : α) (l : List (α × β)) : Option (α × β) :=
  (l.filter fun p => p.1 < k).getLast?

/-- The least entry with key strictly above `k`. -/
def succ? (k : α) (l : List (α × β)) : Option (α × β) :=
  (l.filter fun p => k < p.1).head?

/-- Restriction to the closed key interval `[lo, hi]`. -/
def range (lo hi : α) (l : List (α × β)) : List (α × β) :=
  l.filter fun p => lo ≤ p.1 ∧ p.1 ≤ hi

/-- The rank of `k`: the number of keys strictly below it. -/
def rank (k : α) (l : List (α × β)) : ℕ :=
  (l.filter fun p => p.1 < k).length

variable {l : List (α × β)} {k k' : α} {v : β}

theorem isSortedAssoc_insert (h : IsSortedAssoc l) : IsSortedAssoc (insert k v l) := sorry

theorem isSortedAssoc_erase (h : IsSortedAssoc l) : IsSortedAssoc (erase k l) := sorry

theorem lookup_insert_self (h : IsSortedAssoc l) : lookup k (insert k v l) = some v := sorry

theorem lookup_insert_of_ne (h : IsSortedAssoc l) (hne : k' ≠ k) :
    lookup k' (insert k v l) = lookup k' l := sorry

theorem lookup_erase_self : lookup k (erase k l) = none := sorry

theorem lookup_erase_of_ne (hne : k' ≠ k) : lookup k' (erase k l) = lookup k' l := sorry

theorem erase_of_lookup_eq_none (h : lookup k l = none) : erase k l = l := sorry

theorem lookup_eq_some_iff (h : IsSortedAssoc l) : lookup k l = some v ↔ (k, v) ∈ l := sorry

theorem length_insert (h : IsSortedAssoc l) :
    (insert k v l).length = if (lookup k l).isSome then l.length else l.length + 1 := sorry

theorem length_erase (h : IsSortedAssoc l) :
    (erase k l).length = if (lookup k l).isSome then l.length - 1 else l.length := sorry

theorem mem_range_iff {lo hi : α} {p : α × β} :
    p ∈ range lo hi l ↔ p ∈ l ∧ lo ≤ p.1 ∧ p.1 ≤ hi := sorry

theorem pred?_eq_some_iff (h : IsSortedAssoc l) {p : α × β} :
    pred? k l = some p ↔ p ∈ l ∧ p.1 < k ∧ ∀ q ∈ l, q.1 < k → q.1 ≤ p.1 := sorry

theorem succ?_eq_some_iff (h : IsSortedAssoc l) {p : α × β} :
    succ? k l = some p ↔ p ∈ l ∧ k < p.1 ∧ ∀ q ∈ l, k < q.1 → p.1 ≤ q.1 := sorry

/-- On a sorted list, the rank is the length of the prefix of keys below `k`. -/
theorem rank_eq_length_takeWhile (h : IsSortedAssoc l) :
    rank k l = (l.takeWhile fun p => decide (p.1 < k)).length := sorry

/-- Splitting a sorted list at a key: the shape of the lemma used at every tree node. -/
theorem isSortedAssoc_append_cons_iff {l₁ l₂ : List (α × β)} :
    IsSortedAssoc (l₁ ++ (k, v) :: l₂) ↔
      IsSortedAssoc l₁ ∧ IsSortedAssoc l₂ ∧ (∀ p ∈ l₁, p.1 < k) ∧ ∀ p ∈ l₂, k < p.1 := sorry

end SortedAssoc

/-! ## Milestone 2: B-tree structure and height -/

/-- A classic B-tree. A node is a first child followed by `(key, value, child)` triples, so a
node with `m` keys has `m + 1` children by construction. `leaf` is the empty tree. -/
inductive BTree (α : Type u) (β : Type v) : Type (max u v) where
  | leaf : BTree α β
  | node (first : BTree α β) (rest : List (α × β × BTree α β)) : BTree α β

namespace BTree

section Structure

variable {α : Type u} {β : Type v} {γ : Type w}

mutual
/-- Entries in key order. -/
def toList : BTree α β → List (α × β)
  | leaf => []
  | node first rest => first.toList ++ toListRest rest
/-- Entries of the triples following a first child. -/
def toListRest : List (α × β × BTree α β) → List (α × β)
  | [] => []
  | (k, v, c) :: rest => (k, v) :: c.toList ++ toListRest rest
end

mutual
/-- Nodes on a root-to-leaf path: the leaf has height `0`. -/
def height : BTree α β → ℕ
  | leaf => 0
  | node first rest => max (first.height + 1) (heightRest rest)
/-- Height contribution of the children in a list of triples. -/
def heightRest : List (α × β × BTree α β) → ℕ
  | [] => 0
  | (_, _, c) :: rest => max (c.height + 1) (heightRest rest)
end

mutual
/-- Map over values. -/
def map (f : β → γ) : BTree α β → BTree α γ
  | leaf => leaf
  | node first rest => node (first.map f) (mapRest f rest)
/-- Map over the values of a list of triples. -/
def mapRest (f : β → γ) : List (α × β × BTree α β) → List (α × γ × BTree α γ)
  | [] => []
  | (k, v, c) :: rest => (k, f v, c.map f) :: mapRest f rest
end

/-- Number of entries. -/
def size (tr : BTree α β) : ℕ := tr.toList.length

/-- Keys in order. -/
def keys (tr : BTree α β) : List α := tr.toList.map Prod.fst

/-- Fold over entries in key order; the specification of any direct recursive fold. -/
def foldl (f : γ → α × β → γ) (init : γ) (tr : BTree α β) : γ := tr.toList.foldl f init

instance : Membership (α × β) (BTree α β) := ⟨fun tr p => p ∈ tr.toList⟩

/-- Keys at the root node. -/
def rootKeys : BTree α β → ℕ
  | leaf => 0
  | node _ rest => rest.length

/-- Children of the root node. -/
def children : BTree α β → List (BTree α β)
  | leaf => []
  | node first rest => first :: rest.map (·.2.2)

/-- Every node satisfies the occupancy bounds of a non-root node of minimum degree `t`. -/
inductive Occupied (t : ℕ) : BTree α β → Prop
  | leaf : Occupied t .leaf
  | node {first : BTree α β} {rest : List (α × β × BTree α β)} :
      t - 1 ≤ rest.length → rest.length ≤ 2 * t - 1 →
      Occupied t first → (∀ e ∈ rest, Occupied t e.2.2) → Occupied t (.node first rest)

/-- All leaves at the same depth: every child of a node has the height of the first child. -/
inductive Balanced : BTree α β → Prop
  | leaf : Balanced .leaf
  | node {first : BTree α β} {rest : List (α × β × BTree α β)} :
      Balanced first → (∀ e ∈ rest, Balanced e.2.2) →
      (∀ e ∈ rest, e.2.2.height = first.height) → Balanced (.node first rest)

/-- Well-formed B-tree of minimum degree `t`: root occupancy, non-root occupancy, equal leaf
depth, and key-sortedness of `toList`. -/
structure IsWF [LinearOrder α] (t : ℕ) (tr : BTree α β) : Prop where
  two_le : 2 ≤ t
  rootKeys_le : tr.rootKeys ≤ 2 * t - 1
  rootKeys_pos : tr ≠ .leaf → 1 ≤ tr.rootKeys
  children : ∀ c ∈ tr.children, Occupied t c
  balanced : Balanced tr
  sorted : SortedAssoc.IsSortedAssoc tr.toList

variable {tr : BTree α β}

theorem mem_iff {p : α × β} : p ∈ tr ↔ p ∈ tr.toList := Iff.rfl

theorem toList_map (f : β → γ) : (tr.map f).toList = tr.toList.map fun p => (p.1, f p.2) := sorry

theorem height_map (f : β → γ) : (tr.map f).height = tr.height := sorry

theorem height_eq_zero_iff : tr.height = 0 ↔ tr = .leaf := sorry

variable [LinearOrder α] {t : ℕ}

/-- Every subtree of a well-formed tree is occupied. -/
theorem IsWF.occupied_of_mem_children (h : IsWF t tr) {c : BTree α β} (hc : c ∈ tr.children) :
    Occupied t c := h.children c hc

/-- Children of a well-formed tree have height one less than the tree. -/
theorem IsWF.height_of_mem_children (h : IsWF t tr) {c : BTree α β} (hc : c ∈ tr.children) :
    c.height + 1 = tr.height := sorry

/-- The classic height bound: `h ≤ log_t ((n + 1) / 2)` with `h = height - 1` for non-empty
trees, written with `Nat.log` and the height convention above. -/
theorem IsWF.height_le_log (h : IsWF t tr) :
    tr.height ≤ Nat.log t ((tr.size + 1) / 2) + 1 := sorry

theorem IsWF.le_size (h : IsWF t tr) (hne : tr ≠ .leaf) :
    2 * t ^ (tr.height - 1) - 1 ≤ tr.size := sorry

theorem IsWF.size_le (h : IsWF t tr) : tr.size ≤ (2 * t) ^ tr.height - 1 := sorry

/-- A root with one key and two leaf children is a well-formed 2-3-4 tree. -/
example : IsWF 2 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf)]) := sorry

/-- A node whose children differ in height is not well-formed for any `t`. -/
example (t : ℕ) :
    ¬ IsWF t (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(1, (), .leaf)]) := sorry

end Structure

/-! ## Milestone 3: search and order queries

Operations are defined once over an arbitrary monad with a comparator `le` and a visit action,
with no order instance in scope. The pure operation is the `Id` instantiation. -/

section QueriesPolymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Within-node linear search: the position of the first key not below `k`. At most one
comparison per key. -/
def slotM (le : α → α → m Bool) (k : α) : List (α × β × BTree α β) → m ℕ
  | [] => pure 0
  | (k', _, _) :: rest => do
    if ← le k k' then pure 0 else return (← slotM le k rest) + 1

/-- Lookup. Walking along a node's triples is free; `visit` fires when the search commits to a
child or stops at a key, so each node is visited once. Equality is two `le` queries. -/
def lookupM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m (Option β)
  | .leaf => pure none
  | .node first [] => do
    visit
    lookupM le visit k first
  | .node first ((k', v, c) :: rest) => do
    if ← le k k' then
      visit
      if ← le k' k then
        pure (some v)
      else
        lookupM le visit k first
    else
      lookupM le visit k (.node c rest)
termination_by tr => sizeOf tr

/-- Membership test. -/
def containsM (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BTree α β) : m Bool := do
  return (← lookupM le visit k tr).isSome

/-- Least entry: follow first children. -/
def minM (visit : m Unit) : BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first rest => do
    visit
    match ← minM visit first with
    | some p => pure (some p)
    | none => pure (rest.head?.map fun e => (e.1, e.2.1))

/-- Greatest entry. -/
def maxM (visit : m Unit) : BTree α β → m (Option (α × β)) := sorry

/-- Greatest entry with key strictly below `k`. -/
def predM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m (Option (α × β)) :=
  sorry

/-- Least entry with key strictly above `k`. -/
def succM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m (Option (α × β)) :=
  sorry

/-- Entries with keys in the closed interval `[lo, hi]`, in key order. -/
def rangeM (le : α → α → m Bool) (visit : m Unit) (lo hi : α) : BTree α β → m (List (α × β)) :=
  sorry

/-- The rank of `k`: the number of keys strictly below it. -/
def rankM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m ℕ := sorry

end QueriesPolymorphic

section QueriesPure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- The decidable comparator of the order, in `Id`. -/
abbrev leI (a b : α) : Id Bool := pure (decide (a ≤ b))

/-- Within-node linear search, pure. -/
def slot (k : α) (rest : List (α × β × BTree α β)) : ℕ := Id.run (slotM leI k rest)

/-- Lookup, pure: the `Id` instantiation, as in CSLib's `idRun_mergeSortM`. -/
def lookup (k : α) (tr : BTree α β) : Option β := Id.run (lookupM leI (pure ()) k tr)

/-- Membership test, pure. -/
def contains (k : α) (tr : BTree α β) : Bool := Id.run (containsM leI (pure ()) k tr)

/-- Least entry, pure. -/
def min? (tr : BTree α β) : Option (α × β) := Id.run (minM (pure ()) tr)

/-- Greatest entry, pure. -/
def max? (tr : BTree α β) : Option (α × β) := Id.run (maxM (pure ()) tr)

/-- Predecessor, pure. -/
def pred? (k : α) (tr : BTree α β) : Option (α × β) := Id.run (predM leI (pure ()) k tr)

/-- Successor, pure. -/
def succ? (k : α) (tr : BTree α β) : Option (α × β) := Id.run (succM leI (pure ()) k tr)

/-- Range restriction, pure. -/
def range (lo hi : α) (tr : BTree α β) : List (α × β) := Id.run (rangeM leI (pure ()) lo hi tr)

/-- Rank, pure. -/
def rank (k : α) (tr : BTree α β) : ℕ := Id.run (rankM leI (pure ()) k tr)

/-! ### Model equations -/

theorem slot_eq_length_takeWhile (k : α) (rest : List (α × β × BTree α β)) :
    slot k rest = (rest.takeWhile fun e => decide (e.1 < k)).length := sorry

theorem lookup_eq (h : IsWF t tr) (k : α) : lookup k tr = SortedAssoc.lookup k tr.toList := sorry

theorem contains_eq (h : IsWF t tr) (k : α) :
    contains k tr = (SortedAssoc.lookup k tr.toList).isSome := sorry

theorem min?_eq (h : IsWF t tr) : min? tr = SortedAssoc.min? tr.toList := sorry

theorem max?_eq (h : IsWF t tr) : max? tr = SortedAssoc.max? tr.toList := sorry

theorem pred?_eq (h : IsWF t tr) (k : α) : pred? k tr = SortedAssoc.pred? k tr.toList := sorry

theorem succ?_eq (h : IsWF t tr) (k : α) : succ? k tr = SortedAssoc.succ? k tr.toList := sorry

theorem range_eq (h : IsWF t tr) (lo hi : α) :
    range lo hi tr = SortedAssoc.range lo hi tr.toList := sorry

theorem rank_eq (h : IsWF t tr) (k : α) : rank k tr = SortedAssoc.rank k tr.toList := sorry

end QueriesPure

/-! ## Milestone 4: insertion and erasure -/

section UpdatesPolymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Insert-or-replace, visiting each node on the search path once. Top-down with pre-emptive
splitting, or bottom-up with overflow, are both acceptable; `t` selects the occupancy bounds. -/
def insertM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    BTree α β → m (BTree α β) := sorry

/-- Erase. Interior keys are replaced by a predecessor or successor entry; erasure is not
restricted to leaves. Siblings inspected for borrowing or merging are visited, so the
node-visit bound of Milestone 6 is a constant multiple of the height. -/
def eraseM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BTree α β → m (BTree α β) := sorry

end UpdatesPolymorphic

section UpdatesPure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Insertion, pure. -/
def insert (t : ℕ) (k : α) (v : β) (tr : BTree α β) : BTree α β :=
  Id.run (insertM t leI (pure ()) k v tr)

/-- Erasure, pure. -/
def erase (t : ℕ) (k : α) (tr : BTree α β) : BTree α β := Id.run (eraseM t leI (pure ()) k tr)

/-- Remove and return the least entry. -/
def eraseMin? (t : ℕ) : BTree α β → Option ((α × β) × BTree α β) := sorry

/-- Remove and return the greatest entry. -/
def eraseMax? (t : ℕ) : BTree α β → Option ((α × β) × BTree α β) := sorry

theorem IsWF.insert (h : IsWF t tr) (k : α) (v : β) : IsWF t (insert t k v tr) := sorry

theorem toList_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList := sorry

theorem height_insert_le (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height ≤ tr.height + 1 := sorry

theorem size_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).size = if (lookup k tr).isSome then tr.size else tr.size + 1 := sorry

theorem IsWF.erase (h : IsWF t tr) (k : α) : IsWF t (erase t k tr) := sorry

theorem toList_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).toList = SortedAssoc.erase k tr.toList := sorry

theorem height_erase_le (h : IsWF t tr) (k : α) : (erase t k tr).height ≤ tr.height := sorry

theorem size_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).size = if (lookup k tr).isSome then tr.size - 1 else tr.size := sorry

theorem eraseMin?_eq (h : IsWF t tr) :
    eraseMin? t tr = tr.toList.head?.map fun p => (p, erase t p.1 tr) := sorry

/-- A root split at `t = 2`: a fourth key into a full root raises the height. -/
example :
    (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).height = 2 := sorry

/-- A root collapse at `t = 2`: erasing the only root key merges its two children. -/
example :
    (erase 2 2 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(1, (), .leaf)]) [(2, (), .node .leaf [(3, (), .leaf)])])).height = 1 :=
  sorry

end UpdatesPure

/-! ## Milestone 5: bulk loading and the tree-map bridge -/

section Bulk

variable {α β : Type} [LinearOrder α] {t : ℕ}

/-- Build a well-formed tree from a sorted list in one pass. -/
def ofSortedList (t : ℕ) (l : List (α × β)) : BTree α β := sorry

theorem toList_ofSortedList (ht : 2 ≤ t) {l : List (α × β)} (h : SortedAssoc.IsSortedAssoc l) :
    (ofSortedList t l).toList = l := sorry

theorem IsWF.ofSortedList (ht : 2 ≤ t) {l : List (α × β)} (h : SortedAssoc.IsSortedAssoc l) :
    IsWF t (ofSortedList t l) := sorry

theorem height_ofSortedList_le (ht : 2 ≤ t) {l : List (α × β)}
    (h : SortedAssoc.IsSortedAssoc l) :
    (ofSortedList t l).height ≤ Nat.log t ((l.length + 1) / 2) + 1 := sorry

/-- Output equality with Lean core's tree map; nothing about its internals is used. -/
theorem toList_ofSortedList_eq_treeMap (ht : 2 ≤ t) {l : List (α × β)}
    (h : SortedAssoc.IsSortedAssoc l) :
    (ofSortedList t l).toList = (Std.TreeMap.ofList l compare).toList := sorry

end Bulk

/-! # Stage 2: costs -/

/-! ## Milestone 6: node-visit bounds

The `TimeM` instantiation: one tick per node visited, comparisons free. Its `ret` is the pure
operation, by `IsMonadHom` from the polymorphic definition. -/

section NodeVisits

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- The pure comparator, in `TimeM`. -/
abbrev leT (a b : α) : TimeM ℕ Bool := pure (decide (a ≤ b))

/-- Lookup, node-visit instrumentation. -/
def lookupT (k : α) (tr : BTree α β) : TimeM ℕ (Option β) := lookupM leT (tick 1) k tr

/-- Membership test, node-visit instrumentation. -/
def containsT (k : α) (tr : BTree α β) : TimeM ℕ Bool := containsM leT (tick 1) k tr

/-- Least entry, node-visit instrumentation. -/
def minT (tr : BTree α β) : TimeM ℕ (Option (α × β)) := minM (tick 1) tr

/-- Greatest entry, node-visit instrumentation. -/
def maxT (tr : BTree α β) : TimeM ℕ (Option (α × β)) := maxM (tick 1) tr

/-- Predecessor, node-visit instrumentation. -/
def predT (k : α) (tr : BTree α β) : TimeM ℕ (Option (α × β)) := predM leT (tick 1) k tr

/-- Successor, node-visit instrumentation. -/
def succT (k : α) (tr : BTree α β) : TimeM ℕ (Option (α × β)) := succM leT (tick 1) k tr

/-- Range restriction, node-visit instrumentation. -/
def rangeT (lo hi : α) (tr : BTree α β) : TimeM ℕ (List (α × β)) :=
  rangeM leT (tick 1) lo hi tr

/-- Insertion, node-visit instrumentation. -/
def insertT (t : ℕ) (k : α) (v : β) (tr : BTree α β) : TimeM ℕ (BTree α β) :=
  insertM t leT (tick 1) k v tr

/-- Erasure, node-visit instrumentation. -/
def eraseT (t : ℕ) (k : α) (tr : BTree α β) : TimeM ℕ (BTree α β) :=
  eraseM t leT (tick 1) k tr

/-- Bulk loading charging one tick per node built. -/
def ofSortedListT (t : ℕ) (l : List (α × β)) : TimeM ℕ (BTree α β) := sorry

/-! ### Transfer: `ret` is the pure operation -/

theorem ret_lookupT (k : α) : ⟪lookupT k tr⟫ = lookup k tr := sorry

theorem ret_rangeT (lo hi : α) : ⟪rangeT lo hi tr⟫ = range lo hi tr := sorry

theorem ret_insertT (k : α) (v : β) : ⟪insertT t k v tr⟫ = insert t k v tr := sorry

theorem ret_eraseT (k : α) : ⟪eraseT t k tr⟫ = erase t k tr := sorry

theorem ret_ofSortedListT (l : List (α × β)) : ⟪ofSortedListT t l⟫ = ofSortedList t l := sorry

/-! ### Node-visit bounds -/

theorem time_lookupT (h : IsWF t tr) (k : α) : (lookupT k tr).time ≤ tr.height := sorry

theorem time_lookupT_le_log (h : IsWF t tr) (k : α) :
    (lookupT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 := sorry

theorem time_minT (h : IsWF t tr) : (minT tr).time ≤ tr.height := sorry

theorem time_maxT (h : IsWF t tr) : (maxT tr).time ≤ tr.height := sorry

theorem time_predT (h : IsWF t tr) (k : α) : (predT k tr).time ≤ tr.height := sorry

theorem time_succT (h : IsWF t tr) (k : α) : (succT k tr).time ≤ tr.height := sorry

/-- Two boundary paths plus at most one node per output entry. -/
theorem time_rangeT (h : IsWF t tr) (lo hi : α) :
    (rangeT lo hi tr).time ≤ 2 * tr.height + (range lo hi tr).length := sorry

theorem time_insertT (h : IsWF t tr) (k : α) (v : β) : (insertT t k v tr).time ≤ tr.height :=
  sorry

/-- Erasure inspects at most one child and two siblings per level under the top-down algorithm
of Cormen et al.; a different algorithm states its own constant. -/
theorem time_eraseT (h : IsWF t tr) (k : α) : (eraseT t k tr).time ≤ 3 * tr.height := sorry

theorem time_ofSortedListT (l : List (α × β)) : (ofSortedListT t l).time ≤ l.length := sorry

end NodeVisits

/-! ## Milestone 7: comparison bounds and the search lower bound

The `FreeM (LEQuery α)` instantiation: every comparison is a query, visits are free. Bounds
stated with `UpperBound` hold over every oracle; the output-sensitive range bound is stated at
the oracle of the real order only. -/

section Comparisons

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- Lookup, comparison instrumentation. -/
def lookupQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option β) :=
  lookupM LEQuery.ask (pure ()) k tr

/-- Range restriction, comparison instrumentation. -/
def rangeQ (lo hi : α) (tr : BTree α β) : FreeM (LEQuery α) (List (α × β)) :=
  rangeM LEQuery.ask (pure ()) lo hi tr

/-- Rank, comparison instrumentation. -/
def rankQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) ℕ := rankM LEQuery.ask (pure ()) k tr

/-- Insertion, comparison instrumentation. -/
def insertQ (t : ℕ) (k : α) (v : β) (tr : BTree α β) : FreeM (LEQuery α) (BTree α β) :=
  insertM t LEQuery.ask (pure ()) k v tr

/-- Erasure, comparison instrumentation. -/
def eraseQ (t : ℕ) (k : α) (tr : BTree α β) : FreeM (LEQuery α) (BTree α β) :=
  eraseM t LEQuery.ask (pure ()) k tr

/-- Well-formed inputs, as the domain of a bounded program. -/
abbrev WFInput (α β : Type) [LinearOrder α] (t : ℕ) := {p : BTree α β × α // IsWF t p.1}

variable [LinearOrder α]

/-- The oracle of the actual order. -/
abbrev orderOracle : {ι : Type} → LEQuery α ι → ι :=
  LEQuery.oracleOf fun a b => decide (a ≤ b)

/-! ### Transfer: `eval` at the order's oracle is the pure operation -/

theorem eval_lookupQ (k : α) : (lookupQ k tr).eval orderOracle = lookup k tr := sorry

theorem eval_rangeQ (lo hi : α) : (rangeQ lo hi tr).eval orderOracle = range lo hi tr := sorry

theorem eval_rankQ (k : α) : (rankQ k tr).eval orderOracle = rank k tr := sorry

theorem eval_insertQ (k : α) (v : β) :
    (insertQ t k v tr).eval orderOracle = insert t k v tr := sorry

theorem eval_eraseQ (k : α) : (eraseQ t k tr).eval orderOracle = erase t k tr := sorry

/-! ### Comparison bounds with linear in-node search -/

theorem countQueries_slotM_le (oracle : {ι : Type} → LEQuery α ι → ι) (k : α)
    (rest : List (α × β × BTree α β)) :
    (slotM LEQuery.ask k rest).countQueries oracle ≤ rest.length := sorry

/-- At most `2t` comparisons at each of at most `height` nodes, over every oracle. -/
theorem lookupQ_upperBound (ht : 2 ≤ t) :
    UpperBound (fun p : WFInput α β t => lookupQ p.1.2 p.1.1) (fun p => p.1.1.height)
      (fun h => 2 * t * h) := sorry

theorem insertQ_upperBound (ht : 2 ≤ t) (v : β) :
    UpperBound (fun p : WFInput α β t => insertQ t p.1.2 v p.1.1) (fun p => p.1.1.height)
      (fun h => 2 * t * h) := sorry

/-- The node-visit constant of erasure times the per-node comparison bound. -/
theorem eraseQ_upperBound (ht : 2 ≤ t) :
    UpperBound (fun p : WFInput α β t => eraseQ t p.1.2 p.1.1) (fun p => p.1.1.height)
      (fun h => 2 * t * (3 * h)) := sorry

/-- Range restriction is output-sensitive, and the output under an arbitrary oracle is not the
output under `≤`, so this bound is stated at the order's oracle only. -/
theorem countQueries_rangeQ_le (h : IsWF t tr) (lo hi : α) :
    (rangeQ lo hi tr).countQueries orderOracle ≤
      2 * t * (2 * tr.height + (range lo hi tr).length) := sorry

end Comparisons

/-! ### Binary in-node search -/

section BinarySearchPolymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Within-node binary search over the same list: at most `⌈log₂ (length + 1)⌉ + 1`
comparisons on any list, and the same answer as `slotM` on sorted keys. Binary search over a
list reduces comparisons and nothing else; neither cost model charges the traversal. -/
def slotBinM (le : α → α → m Bool) (k : α) (rest : List (α × β × BTree α β)) : m ℕ := sorry

/-- Lookup using `slotBinM` at each node instead of the linear walk. -/
def lookupBinM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m (Option β) :=
  sorry

/-- Rank using `slotBinM` at each node. -/
def rankBinM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m ℕ := sorry

end BinarySearchPolymorphic

section BinarySearch

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- The comparison bound holds for every list and every oracle. -/
theorem countQueries_slotBinM_le (oracle : {ι : Type} → LEQuery α ι → ι) (k : α)
    (rest : List (α × β × BTree α β)) :
    (slotBinM LEQuery.ask k rest).countQueries oracle ≤ Nat.clog 2 (rest.length + 1) + 1 :=
  sorry

/-- Lookup with binary in-node search, comparison instrumentation. -/
def lookupBinQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) (Option β) :=
  lookupBinM LEQuery.ask (pure ()) k tr

/-- Rank with binary in-node search, comparison instrumentation. -/
def rankBinQ (k : α) (tr : BTree α β) : FreeM (LEQuery α) ℕ :=
  rankBinM LEQuery.ask (pure ()) k tr

variable [LinearOrder α]

/-- Binary search, pure. -/
def slotBin (k : α) (rest : List (α × β × BTree α β)) : ℕ := Id.run (slotBinM leI k rest)

/-- Lookup with binary in-node search, pure. -/
def lookupBin (k : α) (tr : BTree α β) : Option β := Id.run (lookupBinM leI (pure ()) k tr)

/-- Agreement with linear search needs sorted keys; binary search is not specified on an
unsorted node. -/
theorem slotBin_eq_slot (k : α) {rest : List (α × β × BTree α β)}
    (hs : (rest.map (·.1)).Pairwise (· < ·)) : slotBin k rest = slot k rest := sorry

theorem lookupBin_eq (h : IsWF t tr) (k : α) : lookupBin k tr = lookup k tr := sorry

theorem eval_lookupBinQ (h : IsWF t tr) (k : α) :
    (lookupBinQ k tr).eval orderOracle = lookup k tr := sorry

/-- At most `⌈log₂ (2t)⌉ + 1` comparisons at each node. -/
theorem lookupBinQ_upperBound (ht : 2 ≤ t) :
    UpperBound (fun p : WFInput α β t => lookupBinQ p.1.2 p.1.1) (fun p => p.1.1.height)
      (fun h => (Nat.clog 2 (2 * t) + 1) * h) := sorry

theorem rankBinQ_upperBound (ht : 2 ≤ t) :
    UpperBound (fun p : WFInput α β t => rankBinQ p.1.2 p.1.1) (fun p => p.1.1.height)
      (fun h => (Nat.clog 2 (2 * t) + 1) * h) := sorry

end BinarySearch

/-! ### The comparison lower bound for search -/

section LowerBoundSearch

variable {α : Type}

/-- A comparison-based rank program is correct if, under the oracle of every linear order on
the key type, it returns the number of keys strictly below `k` in a strictly sorted list. -/
def IsRank (prog : List α × α → FreeM (LEQuery α) ℕ) : Prop :=
  ∀ [LinearOrder α] (l : List α) (k : α), l.Pairwise (· < ·) →
    (prog (l, k)).eval (LEQuery.oracleOf fun a b => decide (a ≤ b)) =
      (l.filter fun a => decide (a < k)).length

/-- A comparison-based lookup program is correct if, under the oracle of every linear order on
the key type, it returns `List.lookup` on a strictly sorted list of keys paired with their
positions. -/
def IsLookup (prog : List (α × ℕ) × α → FreeM (LEQuery α) (Option ℕ)) : Prop :=
  ∀ [LinearOrder α] (l : List (α × ℕ)) (k : α), (l.map Prod.fst).Pairwise (· < ·) →
    (prog (l, k)).eval (LEQuery.oracleOf fun a b => decide (a ≤ b)) = List.lookup k l

/-- Any correct comparison-based rank program makes at least `⌈log₂ (n + 1)⌉` comparisons on
some input of `n` keys. The substance is the family: `n + 1` linear orders placing `k` in each
gap give `n + 1` distinct answers, and `FreeM.exists_countQueries_ge_clog` applies with
response cardinality two. -/
theorem IsRank.lowerBound [Infinite α] {prog : List α × α → FreeM (LEQuery α) ℕ}
    (h : IsRank prog) :
    LowerBound prog (fun p => p.1.length) (fun n => Nat.clog 2 (n + 1)) := sorry

/-- The same bound for lookup, with its own family: `k` equal to each of the `n` keys, whose
positions are distinct values, or absent, give `n + 1` distinct answers. The rank bound does
not transfer to lookup by itself; this is a separate target. -/
theorem IsLookup.lowerBound [Infinite α]
    {prog : List (α × ℕ) × α → FreeM (LEQuery α) (Option ℕ)} (h : IsLookup prog) :
    LowerBound prog (fun p => p.1.length) (fun n => Nat.clog 2 (n + 1)) := sorry

end LowerBoundSearch

section MeetingTheBound

variable {α : Type} {t : ℕ}

/-- The B-tree rank program on a bulk-loaded tree is a correct rank program. -/
theorem rankBinQ_isRank (t : ℕ) :
    IsRank fun p : List α × α =>
      rankBinQ p.2 (ofSortedList (β := Unit) t (p.1.map fun k => (k, ()))) := sorry

/-- The B-tree lookup program on a bulk-loaded tree is a correct lookup program. -/
theorem lookupBinQ_isLookup (t : ℕ) :
    IsLookup fun p : List (α × ℕ) × α => lookupBinQ p.2 (ofSortedList t p.1) := sorry

variable [LinearOrder α]

/-- Binary in-node search against the lower bound, with the dependence on `t` explicit: the
ratio to `⌈log₂ (n + 1)⌉` is bounded for fixed `t`. -/
theorem countQueries_rankBinQ_le_log (ht : 2 ≤ t) {l : List α} (hs : l.Pairwise (· < ·)) (k : α)
    (oracle : {ι : Type} → LEQuery α ι → ι) :
    (rankBinQ k (ofSortedList (β := Unit) t (l.map fun k => (k, ())))).countQueries oracle ≤
      (Nat.clog 2 (2 * t) + 1) * (Nat.log t ((l.length + 1) / 2) + 1) := sorry

/-- Linear in-node search against the lower bound: also within a constant factor for fixed `t`,
with a constant that grows like `t / log t`. The target is the pair of explicit inequalities,
not an optimality claim. -/
theorem countQueries_rankQ_le_log (ht : 2 ≤ t) {l : List α} (hs : l.Pairwise (· < ·)) (k : α)
    (oracle : {ι : Type} → LEQuery α ι → ι) :
    (rankQ k (ofSortedList (β := Unit) t (l.map fun k => (k, ())))).countQueries oracle ≤
      2 * t * (Nat.log t ((l.length + 1) / 2) + 1) := sorry

end MeetingTheBound

end BTree

/-! ## Milestone 8: read-only operations behind a node-access oracle

The tree is visible only through `read` queries on an abstract handle type, so the number of
node reads is counted structurally. A reference is `Option H`, with `none` the empty leaf, so
that the empty tree is read zero times, as it is visited zero times; this is what makes the
read count equal to the `TimeM` visit count rather than one more. Comparisons are pure here;
the comparison model is Milestone 7's business. -/

namespace NodeAccess

variable {α β H : Type}

/-- What the oracle reveals about one node: a first child reference and
`(key, value, child reference)` triples. -/
abbrev NodeView (α β H : Type) := Option H × List (α × β × Option H)

/-- The single query: read the node behind a handle. -/
inductive NodeQuery (α β H : Type) : Type → Type where
  | read (h : H) : NodeQuery α β H (NodeView α β H)

/-- A store assigns node contents to handles. -/
abbrev Store (α β H : Type) := H → NodeView α β H

/-- A store as an oracle. -/
def Store.oracle (s : Store α β H) : {ι : Type} → NodeQuery α β H ι → ι
  | _, .read h => s h

mutual
/-- The functional tree a reference denotes in a store. -/
def Denotes (s : Store α β H) : Option H → BTree α β → Prop
  | none, .leaf => True
  | some h, .node first rest => ∃ r₀ rs, s h = (r₀, rs) ∧ Denotes s r₀ first ∧
      DenotesRest s rs rest
  | _, _ => False
/-- Triple-by-triple denotation of the children following a first child. -/
def DenotesRest (s : Store α β H) : List (α × β × Option H) → List (α × β × BTree α β) → Prop
  | [], [] => True
  | (k, v, r) :: rs, (k', v', c) :: rest => k = k' ∧ v = v' ∧ Denotes s r c ∧ DenotesRest s rs rest
  | _, _ => False
end

/-- Lookup through the oracle: one `read` per node visited, comparisons pure. `fuel` bounds the
descent, since handles carry no size. -/
def lookupR [LinearOrder α] (fuel : ℕ) (k : α) (root : Option H) :
    FreeM (NodeQuery α β H) (Option β) := sorry

/-- Range restriction through the oracle. -/
def rangeR [LinearOrder α] (fuel : ℕ) (lo hi : α) (root : Option H) :
    FreeM (NodeQuery α β H) (List (α × β)) := sorry

variable [LinearOrder α] {t fuel : ℕ} {s : Store α β H} {root : Option H} {tr : BTree α β}

theorem eval_lookupR (h : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (k : α) : (lookupR fuel k root).eval s.oracle = BTree.lookup k tr := sorry

/-- Node reads are exactly the `TimeM` visit count: the visit model is structural for queries. -/
theorem countQueries_lookupR (h : BTree.IsWF t tr) (hd : Denotes s root tr)
    (hf : tr.height ≤ fuel) (k : α) :
    (lookupR fuel k root).countQueries s.oracle = (BTree.lookupT k tr).time := sorry

theorem countQueries_lookupR_le (h : BTree.IsWF t tr) (hd : Denotes s root tr)
    (hf : tr.height ≤ fuel) (k : α) :
    (lookupR fuel k root).countQueries s.oracle ≤ tr.height := sorry

theorem eval_rangeR (h : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (lo hi : α) : (rangeR fuel lo hi root).eval s.oracle = BTree.range lo hi tr := sorry

theorem countQueries_rangeR (h : BTree.IsWF t tr) (hd : Denotes s root tr)
    (hf : tr.height ≤ fuel) (lo hi : α) :
    (rangeR fuel lo hi root).countQueries s.oracle = (BTree.rangeT lo hi tr).time := sorry

/-- Range restriction reads at most `2 · height + k` nodes, not `height`. -/
theorem countQueries_rangeR_le (h : BTree.IsWF t tr) (hd : Denotes s root tr)
    (hf : tr.height ≤ fuel) (lo hi : α) :
    (rangeR fuel lo hi root).countQueries s.oracle ≤
      2 * tr.height + (BTree.range lo hi tr).length := sorry

end NodeAccess

/-! # Stage 3: B+-trees -/

/-! ## Milestones 9 to 11: B+-trees (headline signatures)

The read operations and updates follow the polymorphic-definition pattern of Milestones 3 and
4, with the pure instantiation in Milestones 9 and 10 and the `TimeM` and `FreeM`
instantiations in Milestone 11; only the pure operations and a few cost statements are stated
here. -/

/-- A B+-tree. Leaves hold entries; an interior node is a first child followed by
`(separator, child)` pairs. Keys below a separator are strictly smaller than it, and keys in the
child it introduces are at least it. A separator need not occur as a key. -/
inductive BPlusTree (α : Type u) (β : Type v) : Type (max u v) where
  | leaf (entries : List (α × β)) : BPlusTree α β
  | node (first : BPlusTree α β) (rest : List (α × BPlusTree α β)) : BPlusTree α β

namespace BPlusTree

variable {α : Type u} {β : Type v}

mutual
/-- The leaf entry lists in key order; the representation of leaf chaining. -/
def leaves : BPlusTree α β → List (List (α × β))
  | leaf entries => [entries]
  | node first rest => first.leaves ++ leavesRest rest
/-- Leaves of the children in a list of pairs. -/
def leavesRest : List (α × BPlusTree α β) → List (List (α × β))
  | [] => []
  | (_, c) :: rest => c.leaves ++ leavesRest rest
end

/-- Entries in key order. -/
def toList (tr : BPlusTree α β) : List (α × β) := tr.leaves.flatten

/-- Number of entries. -/
def size (tr : BPlusTree α β) : ℕ := tr.toList.length

mutual
/-- Levels: a leaf has height `1`. -/
def height : BPlusTree α β → ℕ
  | leaf _ => 1
  | node first rest => max (first.height + 1) (heightRest rest)
/-- Height contribution of the children in a list of pairs. -/
def heightRest : List (α × BPlusTree α β) → ℕ
  | [] => 0
  | (_, c) :: rest => max (c.height + 1) (heightRest rest)
end

/-- Occupancy of non-root nodes: leaves by entries, interior nodes by separators. -/
inductive Occupied (t : ℕ) : BPlusTree α β → Prop
  | leaf {entries : List (α × β)} :
      t - 1 ≤ entries.length → entries.length ≤ 2 * t - 1 → Occupied t (.leaf entries)
  | node {first : BPlusTree α β} {rest : List (α × BPlusTree α β)} :
      t - 1 ≤ rest.length → rest.length ≤ 2 * t - 1 →
      Occupied t first → (∀ e ∈ rest, Occupied t e.2) → Occupied t (.node first rest)

/-- All leaves at the same depth. -/
inductive Balanced : BPlusTree α β → Prop
  | leaf {entries : List (α × β)} : Balanced (.leaf entries)
  | node {first : BPlusTree α β} {rest : List (α × BPlusTree α β)} :
      Balanced first → (∀ e ∈ rest, Balanced e.2) →
      (∀ e ∈ rest, e.2.height = first.height) → Balanced (.node first rest)

/-- The separator convention at every interior node. -/
inductive Separated [LinearOrder α] : BPlusTree α β → Prop
  | leaf {entries : List (α × β)} : Separated (.leaf entries)
  | node {first : BPlusTree α β} {rest : List (α × BPlusTree α β)} :
      Separated first → (∀ e ∈ rest, Separated e.2) →
      (∀ e ∈ rest, (∀ p ∈ e.2.toList, e.1 ≤ p.1)) →
      (∀ i : Fin rest.length, ∀ j : Fin rest.length, i < j →
        ∀ p ∈ rest[i].2.toList, p.1 < rest[j].1) →
      (∀ e ∈ rest, ∀ p ∈ first.toList, p.1 < e.1) →
      Separated (.node first rest)

/-- Well-formed B+-tree of minimum degree `t`. -/
structure IsWF [LinearOrder α] (t : ℕ) (tr : BPlusTree α β) : Prop where
  two_le : 2 ≤ t
  root : match tr with
    | .leaf entries => entries.length ≤ 2 * t - 1
    | .node first rest => 1 ≤ rest.length ∧ rest.length ≤ 2 * t - 1 ∧
        Occupied t first ∧ ∀ e ∈ rest, Occupied t e.2
  balanced : Balanced tr
  separated : Separated tr
  sorted : SortedAssoc.IsSortedAssoc tr.toList

section Headline

variable [LinearOrder α] {t : ℕ} {tr : BPlusTree α β}

theorem IsWF.height_le_log (h : IsWF t tr) : tr.height ≤ Nat.log t tr.size + 1 := sorry

theorem IsWF.pow_le_size (h : IsWF t tr) (h2 : 2 ≤ tr.height) :
    t ^ (tr.height - 1) ≤ tr.size := sorry

/-! ### Milestone 9: queries, pure -/

/-- Lookup, pure. -/
def lookup (k : α) : BPlusTree α β → Option β := sorry

/-- Range restriction, pure. -/
def range (lo hi : α) : BPlusTree α β → List (α × β) := sorry

theorem lookup_eq (h : IsWF t tr) (k : α) : lookup k tr = SortedAssoc.lookup k tr.toList := sorry

theorem range_eq (h : IsWF t tr) (lo hi : α) :
    range lo hi tr = SortedAssoc.range lo hi tr.toList := sorry

/-- The output of a range query is the restriction of a contiguous run of leaves in which every
leaf contributes and every leaf other than the first and last is returned whole. Without the
last two conjuncts the run could be all of `leaves`. -/
theorem range_eq_flatten_run (h : IsWF t tr) (lo hi : α) :
    ∃ pre run post : List (List (α × β)), tr.leaves = pre ++ run ++ post ∧
      range lo hi tr = (run.map (SortedAssoc.range lo hi)).flatten ∧
      (∀ l ∈ run, SortedAssoc.range lo hi l ≠ []) ∧
      ∀ l ∈ (run.drop 1).dropLast, SortedAssoc.range lo hi l = l := sorry

/-! ### Milestone 10: updates and bulk loading, pure -/

/-- Insert-or-replace, pure. -/
def insert (t : ℕ) (k : α) (v : β) : BPlusTree α β → BPlusTree α β := sorry

/-- Erase; separators stay valid without being present as keys. -/
def erase (t : ℕ) (k : α) : BPlusTree α β → BPlusTree α β := sorry

/-- Bulk loading from a sorted list. -/
def ofSortedList (t : ℕ) (l : List (α × β)) : BPlusTree α β := sorry

theorem IsWF.insert (h : IsWF t tr) (k : α) (v : β) : IsWF t (insert t k v tr) := sorry

theorem toList_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList := sorry

theorem IsWF.erase (h : IsWF t tr) (k : α) : IsWF t (erase t k tr) := sorry

theorem toList_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).toList = SortedAssoc.erase k tr.toList := sorry

theorem toList_ofSortedList (ht : 2 ≤ t) {l : List (α × β)} (h : SortedAssoc.IsSortedAssoc l) :
    (ofSortedList t l).toList = l := sorry

theorem IsWF.ofSortedList (ht : 2 ≤ t) {l : List (α × β)} (h : SortedAssoc.IsSortedAssoc l) :
    IsWF t (ofSortedList t l) := sorry

/-- A B+-tree and a classic B-tree built from the same sorted list have the same entries. -/
theorem toList_ofSortedList_eq_btree {α β : Type} [LinearOrder α] (ht : 2 ≤ t)
    {l : List (α × β)} (h : SortedAssoc.IsSortedAssoc l) :
    (ofSortedList t l).toList = (BTree.ofSortedList t l).toList := sorry

/-! ### Milestone 11: costs -/

/-- Lookup, node-visit instrumentation. -/
def lookupT (k : α) : BPlusTree α β → TimeM ℕ (Option β) := sorry

/-- Range restriction, node-visit instrumentation. -/
def rangeT (lo hi : α) : BPlusTree α β → TimeM ℕ (List (α × β)) := sorry

/-- Insertion, node-visit instrumentation. -/
def insertT (t : ℕ) (k : α) (v : β) : BPlusTree α β → TimeM ℕ (BPlusTree α β) := sorry

/-- Erasure, node-visit instrumentation. -/
def eraseT (t : ℕ) (k : α) : BPlusTree α β → TimeM ℕ (BPlusTree α β) := sorry

theorem ret_lookupT (k : α) : ⟪lookupT k tr⟫ = lookup k tr := sorry

theorem time_lookupT (h : IsWF t tr) (k : α) : (lookupT k tr).time ≤ tr.height := sorry

theorem time_rangeT (h : IsWF t tr) (lo hi : α) :
    (rangeT lo hi tr).time ≤ 2 * tr.height + (range lo hi tr).length := sorry

theorem time_insertT (h : IsWF t tr) (k : α) (v : β) : (insertT t k v tr).time ≤ tr.height :=
  sorry

theorem time_eraseT (h : IsWF t tr) (k : α) : (eraseT t k tr).time ≤ 3 * tr.height := sorry

end Headline

/-- Lookup, comparison instrumentation. -/
def lookupQ {α β : Type} (k : α) : BPlusTree α β → FreeM (LEQuery α) (Option β) := sorry

/-- Well-formed inputs, as the domain of a bounded program. -/
abbrev WFInput (α β : Type) [LinearOrder α] (t : ℕ) := {p : BPlusTree α β × α // IsWF t p.1}

theorem lookupQ_upperBound {α β : Type} [LinearOrder α] {t : ℕ} (ht : 2 ≤ t) :
    UpperBound (fun p : WFInput α β t => lookupQ p.1.2 p.1.1) (fun p => p.1.1.height)
      (fun h => 2 * t * h) := sorry

end BPlusTree

end EpsilonEridani
