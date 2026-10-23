import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
import Cslib.Probability.PMF

/-!
# Private-key encryption: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is `README.md`.
It states, with `sorry`, the targets that can already be written against CSLib and Mathlib.
Targets that need the security-game layer are added here as their definitions land in
EpsilonEridani. Item numbers refer to Katz and Lindell, *Introduction to Modern Cryptography*,
third edition [KL3].
-/

namespace EpsilonEridaniRoadmap.PrivateKeyEncryption

open Cslib.Crypto.Protocols.PerfectSecrecy Cslib.Probability.PMF

/-! ## Layer 0: perfect secrecy -/

/-- [KL3, Definition 2.6 and Lemma 2.7] Perfect secrecy is equivalent to perfect adversarial
indistinguishability: every unbounded eavesdropper, choosing messages `m₀ m₁` and a distinguisher
`A`, guesses the challenge bit with probability exactly one half. -/
theorem perfectlySecret_iff_eavSuccess_eq_half {M K C : Type} (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
      ∀ (m₀ m₁ : M) (A : C → Bool),
        (do
          let b ← uniformOfFintype Bool
          let c ← scheme.ciphertextDist (cond b m₁ m₀)
          return (A c == b) : PMF Bool) true = 1 / 2 := by
  sorry

/-- [KL3, Theorem 2.12] Shannon's theorem, for deterministic schemes with
`|M| = |K| = |C|`: perfect secrecy holds exactly when keys are uniform and each message and
ciphertext are linked by exactly one key. -/
theorem ofPure_perfectlySecret_iff {M K C : Type} [Fintype M] [Fintype K] [Fintype C]
    [Nonempty K] (hMK : Fintype.card M = Fintype.card K) (hKC : Fintype.card K = Fintype.card C)
    (gen : PMF K) (enc : K → M → C) (dec : K → C → M)
    (h : ∀ k, Function.LeftInverse (dec k) (enc k)) :
    (EncScheme.ofPure gen enc dec h).PerfectlySecret ↔
      gen = uniformOfFintype K ∧ ∀ m c, ∃! k, enc k m = c := by
  sorry

/-! ## Layer 4: information-theoretic message authentication -/

/-- [KL3, Theorem 4.22] The affine family `(a, b) ↦ a * m + b` over a finite field is strongly
universal: for distinct messages, the pair of tags is uniform under a uniform key. -/
theorem affine_stronglyUniversal {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {m m' : F} (hm : m ≠ m') (t t' : F) :
    (uniformOfFintype (F × F)).toOuterMeasure
        {k | k.1 * m + k.2 = t ∧ k.1 * m' + k.2 = t'} =
      1 / (Fintype.card F : ENNReal) ^ 2 := by
  sorry

end EpsilonEridaniRoadmap.PrivateKeyEncryption
