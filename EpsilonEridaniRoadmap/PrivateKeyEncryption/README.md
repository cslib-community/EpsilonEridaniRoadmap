# Private-key encryption

The theory of private-key encryption and message authentication in Chapters 2–5 of Katz and
Lindell, *Introduction to Modern Cryptography*, third edition [KL3]: perfect secrecy,
computational secrecy from pseudorandom generators and functions, message authentication codes,
and chosen-ciphertext security through authenticated encryption. Item numbers below are KL3's.

Suggested home: `EpsilonEridani/Crypto/`, following the names and namespace layout of CSLib's
`Cslib/Crypto/`, so that material can move to CSLib by a rename.

## Standing hypotheses

- **Probability.** Distributions are Mathlib's `PMF`. Uniform sampling is CSLib's
  `Cslib.Probability.PMF.uniformOfFintype` and `uniformOfFinset`. Statistical distance is
  CSLib's (`Cslib/Probability/StatisticalDistance.lean`).
- **Security games.** Experiments are `PMF Bool` and security is CSLib's game API (CSLib #1069):
  `Game.Secure` for a class of admissible adversaries, with `Game.SecureWithError` for concrete
  bounds. Negligible functions are CSLib's `Negligible` (CSLib #1068). Every security theorem is
  stated twice: concretely, bounding the advantage of the adversary built by an explicit
  reduction, and asymptotically, for every adversary class closed under that reduction, via
  `Secure.of_reduction_with_loss` (CSLib #1070).
- **Efficient adversaries.** KL3's "probabilistic polynomial-time" is the PPT class of
  [OneWayFunctions](../OneWayFunctions/README.md), Layer 0. Each layer below ends with the PPT
  instances of its asymptotic theorems.
- **Oracle access.** Adversaries with oracle access (CPA, PRF, MAC and CCA games) are programs in
  CSLib's free monad `FreeM` (`Cslib/Foundations/Control/Monad/Free.lean`) over the game's query
  interface, interpreted into `PMF` by the experiment. Query bounds use `FreeM.countQueries`
  (`Cslib/Algorithms/Lean/Query/FreeM.lean`).
- **Lengths.** Message, key and block lengths are functions of the security parameter `n`. Fix
  KL3's positive-length conventions in the definitions (block length at least one), so that no
  theorem needs a separate `n = 0` case.

## What CSLib and Mathlib already have (consume)

- **Perfect secrecy:** `Cslib/Crypto/Protocols/PerfectSecrecy/`: `EncScheme`, `PerfectlySecret`
  (Definition 2.3), `CiphertextIndist` with `perfectlySecret_iff_ciphertextIndist` (Lemma 2.5),
  the one-time pad `otp` with `otp_perfectlySecret` (Construction 2.9, Theorem 2.10) and
  `perfectlySecret_keySpace_ge` (Theorem 2.11).
- **Pseudorandom generators:** `Cslib/Crypto/Primitives/PRG/` (`Defs`, `Basic`, `Asymptotic`).
- **Commitments and secret sharing:** `Cslib/Crypto/Protocols/Commitment/`,
  `Cslib/Crypto/Protocols/SecretSharing/` (not used by this roadmap; listed to fix the boundary).
- **Polynomial growth:** `Cslib/Foundations/Data/Nat/PolynomialBound.lean`.
- **Mathlib:** `PMF` and its monad structure, `SuperpolynomialDecay`, finite fields.

## What is missing (build here)

- The CSLib pull requests listed in [`cslib-dependencies.toml`](../../cslib-dependencies.toml):
  negligible functions (#1068), real-valued PMF lemmas (#1062), statistical distance on arbitrary
  types (#1065), security games (#1069), hybrid arguments (#1070), PRGs with explicit seed and
  ideal distributions (#1071), and games versus statistical distance (#1072). Each is built as a
  stand-in under `EpsilonEridani/Pending/`, following
  [CSLIB_DEPENDENCIES.md](../../CSLIB_DEPENDENCIES.md).
- Every definition and theorem of the layers below other than those listed above.

## The build, in layers

### Layer 0: perfect secrecy

- Definition 2.6, perfect adversarial indistinguishability, and Lemma 2.7, its equivalence with
  perfect secrecy.
- Theorem 2.12 (Shannon's theorem), for deterministic schemes with `|M| = |K| = |C|`.

### Layer 1: security-game foundations

- Stand-ins for CSLib #1068, #1062, #1065, #1069 and #1072.
- Definition 3.4, negligible functions: a bridge lemma showing CSLib's `Negligible` is KL3's
  `∀ c, ∀ᶠ n, f n < n ^ (-c)`, and Proposition 3.6, closure under sums and polynomial factors.

### Layer 2: computational secrecy

- Definition 3.7, private-key encryption schemes indexed by the security parameter, with
  correctness.
- Definitions 3.8 and 3.9, eavesdropping (EAV) security in its success-probability and
  advantage forms, and their equivalence.
- Definition 3.12, semantic security, with Theorems 3.10, 3.11 and 3.13 (EAV security is
  equivalent to semantic security).
- Definition 3.14, pseudorandom generators, as CSLib's PRGs (stand-in for CSLib #1071), and
  Construction 3.17 with Theorem 3.16 (a PRG gives an EAV-secure fixed-length scheme).
- Definition 3.18, multiple-message EAV security, and Proposition 3.19 (some EAV-secure scheme is
  not multiple-message EAV-secure; no stateless deterministic scheme is).

### Layer 3: chosen-plaintext attacks and pseudorandom functions

- Definitions 3.21 and 3.22, CPA security and left-or-right CPA security, and Theorem 3.23 (CPA
  security implies multiple-encryption CPA security), using the hybrid argument (stand-in for
  CSLib #1070).
- Definition 3.24, pseudorandom functions, Definition 3.27, strong pseudorandom permutations,
  and Proposition 3.26 (a pseudorandom permutation is a pseudorandom function), with its
  birthday bound.
- Construction 3.28 with Theorem 3.29 (CPA security from a PRF).
- Modes of operation: Constructions 3.30 and 3.31, Theorem 3.32 (CBC mode) and Theorem 3.33 (CTR
  mode).
- Definitions 3.34 and 3.35, nonce-based encryption and its security.

### Layer 4: message authentication codes

- Definitions 4.1–4.3, MACs, (existential) security and strong security, and Proposition 4.4
  (a secure deterministic MAC with canonical verification is strongly secure).
- Construction 4.5 with Theorem 4.6 (a PRF is a secure fixed-length MAC), and Construction 4.7
  with Theorem 4.8 (domain extension to variable-length messages).
- Construction 4.9 with Theorem 4.10 (CBC-MAC), through Theorem 4.12 and Claim 4.13 (the
  random-function CBC smoothness bound `q² ℓ² / 2ⁿ` for prefix-free queries).
- Information-theoretic MACs: Definitions 4.14, 4.18, 4.19 and 4.23, Theorem 4.17 (the
  length-encoded polynomial hash is `ℓ / |F|`-difference universal), Construction 4.20 with
  Theorem 4.21, Theorem 4.22 (the affine family is strongly universal), Construction 4.24 with
  Theorem 4.25, and Theorem 4.26 (an `ε`-secure one-time MAC has `|K| ≥ ε⁻²`).

### Layer 5: chosen-ciphertext attacks and authenticated encryption (the summit)

- Definitions 5.1–5.4: CCA security, unforgeability of encryption, authenticated encryption, and
  the real-versus-ideal formulation, with Theorem 5.5 relating the last two.
- Construction 5.6 with Theorem 5.7 (encrypt-then-authenticate, from a CPA-secure scheme and a
  strongly secure MAC, is authenticated encryption).

## Worked examples (acceptance criteria)

- The one-time pad satisfies Shannon's theorem's conditions, recovering CSLib's
  `otp_perfectlySecret` from Theorem 2.12.
- The shift cipher on a single letter is perfectly secret, and on two letters is not.
- The PRG-based scheme of Construction 3.17 is EAV-secure but, being deterministic, not
  multiple-message EAV-secure (Proposition 3.19).
- The affine MAC over `ZMod p`, for a prime `p`, is a `1 / p`-secure one-time MAC
  (Theorems 4.21 and 4.22).

## Ordering

Layers 0 and 1 are independent and start immediately. Layer 2 needs Layer 1. Layers 3 and 4
need Layer 2; the information-theoretic part of Layer 4 needs only Mathlib and can start at
once. Layer 5 needs Layers 3 and 4. The PPT instances in each layer need
[OneWayFunctions](../OneWayFunctions/README.md), Layer 0.

## Existing formalizations

- **Katz–Lindell corpus** ([karnseth/katz-lindell](https://github.com/karnseth/katz-lindell),
  Apache 2.0): source-linked Lean statements for the whole book with review and proof status.
  Its statements and accepted proofs for Chapters 2–5 are a reference for the precise form of
  each item; this roadmap specifies the mathematics, and integrating its code is coordinated
  with its author.
- **Complexitylib** ([cslib-community/complexitylib](https://github.com/cslib-community/complexitylib)):
  PPT machinery and security reductions under `Complexity/Crypto/`.

## References

- [KL3] J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd edition, CRC Press, 2021.
- D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.6, 2023 (games and
  statistical distance, as used by CSLib).
- M. Bellare, C. Namprempre, *Authenticated encryption: relations among notions and analysis of
  the generic composition paradigm*, ASIACRYPT 2000.

## Acknowledgements

Karn Seth's Katz–Lindell corpus provides the item inventory this roadmap follows.
