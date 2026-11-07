module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Log

/-!
# Ropes: suggested interfaces

`README.md` is the specification. These declarations illustrate the representation,
independent invariants, shared monadic definitions, and principal theorem shapes.
They do not exhaust any milestone. `sorry` marks a target, not completed library code.
The examples at the end use only concrete definitions and contain no `sorry`.

Height counts internal nodes: both `empty` and a leaf have height zero.
No operation compares elements, and the chunk bound is not a type parameter.
-/

public section

namespace EpsilonEridani

universe u w v

/-- Raw persistent sequence; malformed trees can be written and discussed. -/
inductive Rope (α : Type u) where
  | empty
  | leaf (xs : List α)
  | node (cachedLength cachedHeight : ℕ) (left right : Rope α)

namespace Rope

section Structure

variable {α : Type u}

def length : Rope α → ℕ
  | .empty => 0
  | .leaf xs => xs.length
  | .node n _ _ _ => n

def height : Rope α → ℕ
  | .empty | .leaf _ => 0
  | .node _ h _ _ => h

def structuralHeight : Rope α → ℕ
  | .empty | .leaf _ => 0
  | .node _ _ l r => max l.structuralHeight r.structuralHeight + 1

def leaves : Rope α → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ l r => l.leaves + r.leaves

def isEmpty : Rope α → Bool
  | .empty => true
  | _ => false

def CacheCorrect : Rope α → Prop
  | .empty | .leaf _ => True
  | .node n h l r =>
    CacheCorrect l ∧ CacheCorrect r ∧ n = l.length + r.length ∧
      h = max l.height r.height + 1

def Chunked (B : ℕ) : Rope α → Prop
  | .empty => True
  | .leaf xs => 0 < xs.length ∧ xs.length ≤ B
  | .node _ _ l r =>
    Chunked B l ∧ Chunked B r ∧ l.isEmpty = false ∧ r.isEmpty = false

def Balanced : Rope α → Prop
  | .empty | .leaf _ => True
  | .node _ _ l r =>
    Balanced l ∧ Balanced r ∧
      l.structuralHeight ≤ r.structuralHeight + 1 ∧
      r.structuralHeight ≤ l.structuralHeight + 1

def IsWF (B : ℕ) (t : Rope α) : Prop :=
  CacheCorrect t ∧ Chunked B t ∧ Balanced t

instance instDecidableCacheCorrect (t : Rope α) : Decidable (CacheCorrect t) :=
  match t with
  | .empty | .leaf _ => inferInstanceAs (Decidable True)
  | .node n h l r =>
    haveI := instDecidableCacheCorrect l
    haveI := instDecidableCacheCorrect r
    inferInstanceAs (Decidable (CacheCorrect l ∧ CacheCorrect r ∧
      n = l.length + r.length ∧ h = max l.height r.height + 1))

instance instDecidableChunked (B : ℕ) (t : Rope α) : Decidable (Chunked B t) :=
  match t with
  | .empty => inferInstanceAs (Decidable True)
  | .leaf xs => inferInstanceAs (Decidable (0 < xs.length ∧ xs.length ≤ B))
  | .node _ _ l r =>
    haveI := instDecidableChunked B l
    haveI := instDecidableChunked B r
    inferInstanceAs (Decidable (Chunked B l ∧ Chunked B r ∧
      l.isEmpty = false ∧ r.isEmpty = false))

instance instDecidableBalanced (t : Rope α) : Decidable (Balanced t) :=
  match t with
  | .empty | .leaf _ => inferInstanceAs (Decidable True)
  | .node _ _ l r =>
    haveI := instDecidableBalanced l
    haveI := instDecidableBalanced r
    inferInstanceAs (Decidable (Balanced l ∧ Balanced r ∧
      l.structuralHeight ≤ r.structuralHeight + 1 ∧
      r.structuralHeight ≤ l.structuralHeight + 1))

instance (B : ℕ) (t : Rope α) : Decidable (IsWF B t) :=
  inferInstanceAs (Decidable (CacheCorrect t ∧ Chunked B t ∧ Balanced t))

/-- Recompute caches and eliminate empty children; this does not rotate. -/
def mkNode : Rope α → Rope α → Rope α
  | .empty, r => r
  | l, .empty => l
  | l, r => .node (l.length + r.length) (max l.height r.height + 1) l r

theorem cacheCorrect_node_iff (n h : ℕ) (l r : Rope α) :
    CacheCorrect (.node n h l r) ↔
      CacheCorrect l ∧ CacheCorrect r ∧ n = l.length + r.length ∧
        h = max l.height r.height + 1 := Iff.rfl

theorem chunked_node_iff (B n h : ℕ) (l r : Rope α) :
    Chunked B (.node n h l r) ↔
      Chunked B l ∧ Chunked B r ∧ l.isEmpty = false ∧ r.isEmpty = false := Iff.rfl

theorem balanced_node_iff (n h : ℕ) (l r : Rope α) :
    Balanced (.node n h l r) ↔
      Balanced l ∧ Balanced r ∧ l.structuralHeight ≤ r.structuralHeight + 1 ∧
        r.structuralHeight ≤ l.structuralHeight + 1 := Iff.rfl

theorem height_eq_structuralHeight {t : Rope α} (h : CacheCorrect t) :
    t.height = t.structuralHeight := sorry

end Structure

/-! ## M1: executable basic API, parameterized by the charging action -/

section Basic

variable {α β γ : Type} {m : Type → Type w} [Monad m]

/-- Right-to-left accumulator traversal; each leaf list is copied exactly once. -/
def toListAuxM (tick : ℕ → m Unit) : Rope α → List α → m (List α)
  | .empty, tail => pure tail
  | .leaf xs, tail => do
    tick xs.length
    pure (xs ++ tail)
  | .node _ _ l r, tail => do
    tick 1
    let suffix ← toListAuxM tick r tail
    toListAuxM tick l suffix

def toListM (tick : ℕ → m Unit) (t : Rope α) : m (List α) :=
  toListAuxM tick t []

/-- Leaf indexing is free in the stipulated structural cost model. -/
def get?M (tick : ℕ → m Unit) : Rope α → ℕ → m (Option α)
  | .empty, _ => pure none
  | .leaf xs, i => pure xs[i]?
  | .node _ _ l r, i => do
    tick 1
    if i < l.length then get?M tick l i else get?M tick r (i - l.length)

def mapM (tick : ℕ → m Unit) (f : α → β) : Rope α → m (Rope β)
  | .empty => pure .empty
  | .leaf xs => do
    tick xs.length
    pure (.leaf (xs.map f))
  | .node n h l r => do
    tick 1
    let l' ← mapM tick f l
    let r' ← mapM tick f r
    pure (.node n h l' r')

def foldlM (tick : ℕ → m Unit) (f : β → α → β) (z : β) : Rope α → m β
  | .empty => pure z
  | .leaf xs => pure (xs.foldl f z)
  | .node _ _ l r => do
    tick 1
    let z' ← foldlM tick f z l
    foldlM tick f z' r

def foldrM (tick : ℕ → m Unit) (f : α → β → β) (z : β) : Rope α → m β
  | .empty => pure z
  | .leaf xs => pure (xs.foldr f z)
  | .node _ _ l r => do
    tick 1
    let z' ← foldrM tick f z r
    foldrM tick f z' l

/-- Bulk chunks of size `max 1 B`, except possibly the last; balanced construction. -/
def ofListM (tick : ℕ → m Unit) (B : ℕ) (xs : List α) : m (Rope α) := sorry

def singletonM (tick : ℕ → m Unit) (x : α) : m (Rope α) := do
  tick 1
  pure (.leaf [x])

end Basic

section PureBasic

variable {α β : Type}

def tickI (_ : ℕ) : Id Unit := pure ()

def toList (t : Rope α) : List α := Id.run (toListM tickI t)
def get? (t : Rope α) (i : ℕ) : Option α := Id.run (get?M tickI t i)
def map (f : α → β) (t : Rope α) : Rope β := Id.run (mapM tickI f t)
def foldl (f : β → α → β) (z : β) (t : Rope α) : β := Id.run (foldlM tickI f z t)
def foldr (f : α → β → β) (z : β) (t : Rope α) : β := Id.run (foldrM tickI f z t)
def ofList (B : ℕ) (xs : List α) : Rope α := Id.run (ofListM tickI B xs)
def singleton (x : α) : Rope α := Id.run (singletonM tickI x)

instance : Membership α (Rope α) := ⟨fun t x => x ∈ t.toList⟩

theorem mem_iff (x : α) (t : Rope α) : x ∈ t ↔ x ∈ t.toList := Iff.rfl

theorem toList_node (n h : ℕ) (l r : Rope α) :
    toList (.node n h l r) = l.toList ++ r.toList := sorry

theorem length_eq_toList_length {t : Rope α} (hc : CacheCorrect t) :
    t.length = t.toList.length := sorry

theorem get?_eq {t : Rope α} (hc : CacheCorrect t) (i : ℕ) :
    t.get? i = t.toList[i]? := sorry

theorem toList_map (f : α → β) (t : Rope α) :
    (map f t).toList = t.toList.map f := sorry

theorem isWF_map {B : ℕ} {t : Rope α} (h : IsWF B t) (f : α → β) :
    IsWF B (map f t) := sorry

theorem foldl_eq (f : β → α → β) (z : β) (t : Rope α) :
    foldl f z t = t.toList.foldl f z := sorry

theorem foldr_eq (f : α → β → β) (z : β) (t : Rope α) :
    foldr f z t = t.toList.foldr f z := sorry

theorem toList_ofList (B : ℕ) (xs : List α) : (ofList B xs).toList = xs := sorry

theorem isWF_ofList {B : ℕ} (hB : 1 ≤ B) (xs : List α) :
    IsWF B (ofList B xs) := sorry

end PureBasic

/-! ## M2–M4: rotations, join, split, and height effects -/

def heightDiff (a b : ℕ) : ℕ := (a - b) + (b - a)
def heightBound (n : ℕ) : ℕ := 2 * Nat.log 2 (n + 1)

section StructuralOperations

variable {α : Type} {m : Type → Type w} [Monad m]

/-- Single/double rotation node, requiring height difference at most two in its theorems. -/
def balanceNodeM (tick : ℕ → m Unit) (l r : Rope α) : m (Rope α) := sorry

/-- Spine join via `balanceNodeM`; never copies or merges leaves. -/
def joinM (tick : ℕ → m Unit) (l r : Rope α) : m (Rope α) := sorry

/-- One descent, at most one cut leaf, then joins on return. -/
def splitAtM (tick : ℕ → m Unit) (t : Rope α) (i : ℕ) : m (Rope α × Rope α) := sorry

end StructuralOperations

section StructuralTheorems

variable {α : Type} {B : ℕ} {t l r : Rope α}

def balanceNode (l r : Rope α) : Rope α := Id.run (balanceNodeM tickI l r)
def join (l r : Rope α) : Rope α := Id.run (joinM tickI l r)
abbrev append (l r : Rope α) : Rope α := join l r
def splitAt (t : Rope α) (i : ℕ) : Rope α × Rope α := Id.run (splitAtM tickI t i)

theorem leaves_le_length (h : IsWF B t) : t.leaves ≤ t.length := sorry

/-- Leaf height zero gives `fib (h + 2) ≤ leaves` for non-empty trees. -/
theorem fib_height_le_leaves (h : IsWF B t) (hne : t.isEmpty = false) :
    Nat.fib (t.height + 2) ≤ t.leaves := sorry

theorem height_le_log (h : IsWF B t) : t.height ≤ heightBound t.length := sorry

theorem isWF_balanceNode (hl : IsWF B l) (hr : IsWF B r)
    (hd : heightDiff l.height r.height ≤ 2) : IsWF B (balanceNode l r) := sorry

theorem toList_balanceNode (hl : IsWF B l) (hr : IsWF B r)
    (hd : heightDiff l.height r.height ≤ 2) :
    (balanceNode l r).toList = l.toList ++ r.toList := sorry

theorem toList_join (hl : IsWF B l) (hr : IsWF B r) :
    (join l r).toList = l.toList ++ r.toList := sorry

theorem isWF_join (hl : IsWF B l) (hr : IsWF B r) : IsWF B (join l r) := sorry

theorem height_join (hl : IsWF B l) (hr : IsWF B r)
    (hln : l.isEmpty = false) (hrn : r.isEmpty = false) :
    max l.height r.height ≤ (join l r).height ∧
      (join l r).height ≤ max l.height r.height + 1 := sorry

theorem toList_splitAt (h : IsWF B t) (i : ℕ) :
    (splitAt t i).1.toList = t.toList.take i ∧
      (splitAt t i).2.toList = t.toList.drop i := sorry

theorem isWF_splitAt (h : IsWF B t) (i : ℕ) :
    IsWF B (splitAt t i).1 ∧ IsWF B (splitAt t i).2 := sorry

theorem length_splitAt (h : IsWF B t) (i : ℕ) :
    (splitAt t i).1.length = min i t.length ∧
      (splitAt t i).2.length = t.length - i := sorry

theorem height_splitAt (h : IsWF B t) (i : ℕ) :
    (splitAt t i).1.height ≤ t.height ∧ (splitAt t i).2.height ≤ t.height := sorry

end StructuralTheorems

/-! ## M5–M6: edits and bridges use the same monadic primitives -/

section DerivedOperations

variable {α : Type} {m : Type → Type w} [Monad m]

def insertAtM (tick : ℕ → m Unit) (t : Rope α) (i : ℕ) (x : α) : m (Rope α) := do
  if t.length < i then return t
  let (p, q) ← splitAtM tick t i
  let one ← singletonM tick x
  let u ← joinM tick p one
  joinM tick u q

def extractM (tick : ℕ → m Unit) (t : Rope α) (i j : ℕ) : m (Rope α) := do
  let (_, q) ← splitAtM tick t i
  let (middle, _) ← splitAtM tick q (j - i)
  pure middle

def eraseM (tick : ℕ → m Unit) (t : Rope α) (i j : ℕ) : m (Rope α) := do
  if j < i then return t
  let (p, q) ← splitAtM tick t i
  let (_, r) ← splitAtM tick q (j - i)
  joinM tick p r

def setM (tick : ℕ → m Unit) (t : Rope α) (i : ℕ) (x : α) : m (Rope α) := do
  if t.length ≤ i then return t
  let (p, q) ← splitAtM tick t i
  let (_, r) ← splitAtM tick q 1
  let one ← singletonM tick x
  let u ← joinM tick p one
  joinM tick u r

def compactM (tick : ℕ → m Unit) (B : ℕ) (t : Rope α) : m (Rope α) := do
  ofListM tick B (← toListM tick t)

def ofStringM (tick : ℕ → m Unit) (B : ℕ) (s : String) : m (Rope Char) :=
  ofListM tick B s.toList

def toStringM (tick : ℕ → m Unit) (t : Rope Char) : m String := do
  pure (String.ofList (← toListM tick t))

end DerivedOperations

section DerivedTheorems

variable {α : Type} {B : ℕ} {t : Rope α}

def insertAt (t : Rope α) (i : ℕ) (x : α) : Rope α := Id.run (insertAtM tickI t i x)
def extract (t : Rope α) (i j : ℕ) : Rope α := Id.run (extractM tickI t i j)
def erase (t : Rope α) (i j : ℕ) : Rope α := Id.run (eraseM tickI t i j)
def set (t : Rope α) (i : ℕ) (x : α) : Rope α := Id.run (setM tickI t i x)
def compact (B : ℕ) (t : Rope α) : Rope α := Id.run (compactM tickI B t)
def ofString (B : ℕ) (s : String) : Rope Char := Id.run (ofStringM tickI B s)
def toString (t : Rope Char) : String := Id.run (toStringM tickI t)

theorem toList_insertAt (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) (x : α) :
    (insertAt t i x).toList = t.toList.insertIdx i x := sorry

theorem toList_set (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) (x : α) :
    (set t i x).toList = t.toList.set i x := sorry

theorem toList_extract (h : IsWF B t) (i j : ℕ) :
    (extract t i j).toList = t.toList.extract i j := sorry

theorem toList_erase (h : IsWF B t) (i j : ℕ) :
    (erase t i j).toList = if j < i then t.toList else t.toList.take i ++ t.toList.drop j := sorry

theorem isWF_insertAt (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) (x : α) :
    IsWF B (insertAt t i x) := sorry

theorem isWF_set (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) (x : α) :
    IsWF B (set t i x) := sorry

theorem isWF_extract (h : IsWF B t) (i j : ℕ) : IsWF B (extract t i j) := sorry

theorem isWF_erase (h : IsWF B t) (i j : ℕ) : IsWF B (erase t i j) := sorry

theorem toList_compact (B : ℕ) (t : Rope α) : (compact B t).toList = t.toList := sorry

theorem toString_ofString (B : ℕ) (s : String) : toString (ofString B s) = s := sorry

theorem toList_ofString_toString (B : ℕ) (t : Rope Char) :
    (ofString B (toString t)).toList = t.toList := sorry

end DerivedTheorems

/-! ## M7–M10: instrumented aliases, transfer, and representative cost targets -/

section Costs

open Cslib.Algorithms.Lean (TimeM)

variable {α β : Type} {B : ℕ} {t l r : Rope α}

/-- `TimeM.tick` returns `PUnit`; the operation interface deliberately takes `Unit`. -/
def tickT (n : ℕ) : TimeM ℕ Unit := do
  Cslib.Algorithms.Lean.TimeM.tick n
  pure ()

def get?T (t : Rope α) (i : ℕ) : TimeM ℕ (Option α) := get?M tickT t i
def joinT (l r : Rope α) : TimeM ℕ (Rope α) := joinM tickT l r
def splitAtT (t : Rope α) (i : ℕ) : TimeM ℕ (Rope α × Rope α) := splitAtM tickT t i

def joinBound (a b : ℕ) : ℕ := 8 * (heightDiff a b + 1)
def splitBound (h B : ℕ) : ℕ := 64 * h + B + 8

/-- The homomorphism must map the tick action as well as the monadic structure. -/
theorem map_get?M {m : Type → Type w} {n : Type → Type v} [Monad m] [Monad n]
    {φ : {δ : Type} → m δ → n δ} (hφ : Cslib.IsMonadHom m n φ)
    (tm : ℕ → m Unit) (tn : ℕ → n Unit) (htick : ∀ k, φ (tm k) = tn k)
    (t : Rope α) (i : ℕ) : φ (get?M tm t i) = get?M tn t i := by
  induction t generalizing i with
  | empty => exact hφ.map_pure _
  | leaf xs => exact hφ.map_pure _
  | node len ht l r ihl ihr =>
    simp only [get?M, hφ.map_bind, htick]
    congr 1
    funext _
    split
    · exact ihl i
    · exact ihr (i - l.length)

theorem ret_get?T (t : Rope α) (i : ℕ) : (get?T t i).ret = get? t i := by
  have h := map_get?M (Cslib.Algorithms.Lean.TimeM.isMonadHom_pure_ret (T := ℕ))
    tickT tickI (fun _ => rfl) t i
  exact congrArg Id.run h

theorem ret_joinT (l r : Rope α) : (joinT l r).ret = join l r := sorry

theorem ret_splitAtT (t : Rope α) (i : ℕ) : (splitAtT t i).ret = splitAt t i := sorry

theorem time_get?T (h : IsWF B t) (i : ℕ) : (get?T t i).time ≤ t.height := sorry

theorem time_get?T_log (h : IsWF B t) (i : ℕ) :
    (get?T t i).time ≤ heightBound t.length := sorry

theorem time_toListM (h : IsWF B t) : (toListM tickT t).time ≤ 2 * t.length + 1 := sorry

theorem time_mapM (h : IsWF B t) (f : α → β) :
    (mapM tickT f t).time ≤ 2 * t.length + 1 := sorry

theorem time_foldlM (h : IsWF B t) (f : β → α → β) (z : β) :
    (foldlM tickT f z t).time ≤ t.length := sorry

theorem time_ofListM (hB : 1 ≤ B) (xs : List α) :
    (ofListM tickT B xs).time ≤ 4 * xs.length + 1 := sorry

theorem time_balanceNodeM (hl : IsWF B l) (hr : IsWF B r)
    (hd : heightDiff l.height r.height ≤ 2) : (balanceNodeM tickT l r).time ≤ 8 := sorry

theorem time_joinT (hl : IsWF B l) (hr : IsWF B r) :
    (joinT l r).time ≤ joinBound l.height r.height := sorry

theorem time_splitAtT (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) :
    (splitAtT t i).time ≤ splitBound t.height B := sorry

theorem time_splitAtT_log (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) :
    (splitAtT t i).time ≤ 128 * Nat.log 2 (t.length + 1) + B + 8 := sorry

/-- One split, one singleton copy, and two joins; no fresh edit-specific constant. -/
theorem time_insertAtM (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) (x : α)
    (hi : i ≤ t.length) :
    let p := (splitAt t i).1
    let q := (splitAt t i).2
    let one := singleton x
    let u := join p one
    (insertAtM tickT t i x).time ≤ splitBound t.height B + 1 +
      joinBound p.height one.height + joinBound u.height q.height := sorry

theorem time_extractM (hB : 1 ≤ B) (h : IsWF B t) (i j : ℕ) :
    (extractM tickT t i j).time ≤
      splitBound t.height B + splitBound (splitAt t i).2.height B := sorry

theorem time_eraseM (hB : 1 ≤ B) (h : IsWF B t) (i j : ℕ) (hij : i ≤ j) :
    let p := (splitAt t i).1
    let q := (splitAt t i).2
    let r := (splitAt q (j - i)).2
    (eraseM tickT t i j).time ≤ splitBound t.height B + splitBound q.height B +
      joinBound p.height r.height := sorry

theorem time_setM (hB : 1 ≤ B) (h : IsWF B t) (i : ℕ) (x : α) (hi : i < t.length) :
    let p := (splitAt t i).1
    let q := (splitAt t i).2
    let r := (splitAt q 1).2
    let one := singleton x
    let u := join p one
    (setM tickT t i x).time ≤ splitBound t.height B + splitBound q.height B + 1 +
      joinBound p.height one.height + joinBound u.height r.height := sorry

theorem time_compactM (hB : 1 ≤ B) (h : IsWF B t) :
    (compactM tickT B t).time ≤ (2 * t.length + 1) + (4 * t.length + 1) := sorry

end Costs

/-! ## Checked examples: invariant components and core boundary semantics -/

private def small : Rope Nat := .node 3 1 (.leaf [10, 20]) (.leaf [30])

example : IsWF 2 small := by decide
example : ¬ Chunked 1 small := by decide
example : toList small = [10, 20, 30] := rfl
example : get? small 0 = some 10 := rfl
example : get? small 3 = none := rfl
example : toList (map (· + 1) small) = [11, 21, 31] := rfl
example : (get?T small 1).time = 1 := rfl
example : (toListM tickT small).time = 4 := rfl
example : (mapM tickT (fun x => x + 1) small).time = 4 := rfl
example : IsWF 1 (.node 2 1 (.leaf [10]) (.leaf [20]) : Rope Nat) := by decide

-- Each malformed tree isolates a different predicate failure.
example : ¬ CacheCorrect (.node 99 1 (.leaf [10]) (.leaf [20]) : Rope Nat) := by decide
example : ¬ CacheCorrect (.node 2 99 (.leaf [10]) (.leaf [20]) : Rope Nat) := by decide
example : CacheCorrect (.leaf [10, 20, 30] : Rope Nat) := by decide
example : ¬ Chunked 2 (.leaf [10, 20, 30] : Rope Nat) := by decide
example : ¬ Chunked 2 (.leaf [] : Rope Nat) := by decide
example : CacheCorrect (.node 1 1 .empty (.leaf [10]) : Rope Nat) := by decide
example : ¬ Chunked 2 (.node 1 1 .empty (.leaf [10]) : Rope Nat) := by decide

private def skew : Rope Nat :=
  mkNode (mkNode (mkNode (.leaf [1]) (.leaf [2])) (.leaf [3])) (.leaf [4])

example : CacheCorrect skew ∧ Chunked 1 skew := by decide
example : ¬ Balanced skew := by decide
example : structuralHeight (Rope.empty : Rope Nat) = 0 := rfl
example : structuralHeight (.leaf [1] : Rope Nat) = 0 := rfl

-- These reduce in core, independent of the unfinished join/split prototypes.
example : ([10, 20] : List Nat).insertIdx 2 30 = [10, 20, 30] := rfl
example : ([10, 20] : List Nat).insertIdx 3 30 = [10, 20] := rfl
example : ([10, 20] : List Nat).set 2 30 = [10, 20] := rfl
example : ([10, 20, 30] : List Nat).extract 2 1 = [] := rfl
example : ([10, 20] : List Nat).take 9 = [10, 20] := rfl
example : ([10, 20] : List Nat).drop 9 = [] := rfl
-- Unguarded reversed erasure would duplicate 20; the API instead returns the input.
example : ([10, 20, 30] : List Nat).take 2 ++ [10, 20, 30].drop 1 = [10, 20, 20, 30] := rfl

end Rope
end EpsilonEridani
