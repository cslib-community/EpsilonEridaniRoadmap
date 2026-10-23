import Mathlib

/-!
# One-way functions and pseudorandomness: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is `README.md`.
It states, with `sorry`, the targets that can already be written against CSLib and Mathlib.
Targets that need the PPT layer are added here as their definitions land in EpsilonEridani. Item
numbers refer to Katz and Lindell, *Introduction to Modern Cryptography*, third edition [KL3].
-/

namespace EpsilonEridaniRoadmap.OneWayFunctions

open Finset

/-! ## Layer 2: the averaging steps of the Goldreich–Levin theorem -/

/-- [KL3, Claim 8.14] If success probabilities `s x ≤ 1` average at least `3/4 + ε`, then at least
an `ε / 2` fraction of the inputs have success at least `3/4 + ε / 2`. -/
theorem card_filter_ge_three_quarters {ι : Type} [Fintype ι] (s : ι → ℝ) (hs : ∀ x, s x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (havg : (3 / 4 + ε) * Fintype.card ι ≤ ∑ x, s x) :
    ε / 2 * Fintype.card ι ≤ (univ.filter fun x => 3 / 4 + ε / 2 ≤ s x).card := by
  sorry

/-- [KL3, Claim 8.17] If success probabilities `s x ≤ 1` average at least `1/2 + ε`, then at least
an `ε / 2` fraction of the inputs have success at least `1/2 + ε / 2`. -/
theorem card_filter_ge_half {ι : Type} [Fintype ι] (s : ι → ℝ) (hs : ∀ x, s x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (havg : (1 / 2 + ε) * Fintype.card ι ≤ ∑ x, s x) :
    ε / 2 * Fintype.card ι ≤ (univ.filter fun x => 1 / 2 + ε / 2 ≤ s x).card := by
  sorry

end EpsilonEridaniRoadmap.OneWayFunctions
