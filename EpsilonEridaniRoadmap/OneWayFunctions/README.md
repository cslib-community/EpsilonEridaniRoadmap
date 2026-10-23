# One-way functions and pseudorandomness

The theoretical constructions of Chapter 8 of Katz and Lindell, *Introduction to Modern
Cryptography*, third edition [KL3]: efficient probabilistic computation, one-way functions and
hard-core predicates, the Goldreich–Levin theorem, and the constructions of pseudorandom
generators, functions and permutations from one-way permutations. Item numbers below are KL3's.

Suggested home: `EpsilonEridani/Crypto/` and `EpsilonEridani/Computability/Probabilistic/`,
following CSLib's names and namespace layout.

## Standing hypotheses

- The standing hypotheses of [PrivateKeyEncryption](../PrivateKeyEncryption/README.md) apply:
  `PMF` probability, CSLib's security games and negligible functions, and oracle access through
  CSLib's `FreeM`.
- **Bit strings.** Inputs, outputs and seeds are `List Bool` or `BitVec` values whose lengths are
  functions of the security parameter `n`. Fix one representation in Layer 0 and give the
  equivalence with the other.
- **Efficiency is a class of machines, not an assumption on functions.** "Polynomial time" and
  "PPT" refer to machines over CSLib's Turing machines with explicit time bounds, never to an
  abstract predicate on Lean functions. Reductions are stated as explicit machines built from the
  adversary, with their running time and success probability.
- **Uniformity.** KL3's adversaries are uniform PPT machines; nonuniform variants are not part of
  this roadmap.

## What CSLib and Mathlib already have (consume)

- **Machines:** CSLib's Turing machines with time and space bounds
  (`Cslib/Computability/Machines/`), and polynomial growth
  (`Cslib/Foundations/Data/Nat/PolynomialBound.lean`).
- **Oracle programs:** `FreeM` (`Cslib/Foundations/Control/Monad/Free.lean`) and its query
  counters (`Cslib/Algorithms/Lean/Query/FreeM.lean`).
- **Pseudorandom generators and games:** `Cslib/Crypto/Primitives/PRG/`, and the CSLib pull
  requests listed in [`cslib-dependencies.toml`](../../cslib-dependencies.toml), built as
  stand-ins by [PrivateKeyEncryption](../PrivateKeyEncryption/README.md), Layer 1.
- **From [PrivateKeyEncryption](../PrivateKeyEncryption/README.md):** pseudorandom generators
  (Definition 3.14, Layer 2), pseudorandom functions and strong pseudorandom permutations
  (Definitions 3.24 and 3.27, Layer 3), and authenticated encryption (Layer 5).

## What is missing (build here)

Every definition and theorem of the layers below.

## The build, in layers

### Layer 0: efficient probabilistic computation

- Probabilistic polynomial-time machines: CSLib Turing machines reading a random tape, with a
  polynomial time bound, and the `PMF` of their output on each input.
- Deterministic polynomial-time computable functions on bit strings, closed under composition,
  pairing and polynomially bounded iteration.
- PPT oracle machines, and composition: substituting a PPT machine for an oracle gives a PPT
  machine, with the composed time bound.
- The class of PPT adversaries as an admissibility predicate for CSLib's `Game.Secure`, closed
  under composition with PPT reductions, so that `Secure.of_reduction_with_loss` applies.
- Definition 8.29, computational indistinguishability of ensembles, and Theorem 8.31
  (polynomially many independent samples of efficiently sampleable indistinguishable ensembles
  remain indistinguishable), by the hybrid argument.

### Layer 1: one-way functions and hard-core predicates

- Definitions 8.1–8.3: one-way functions, function and permutation families, and one-way
  families.
- Definition 8.4, hard-core predicates.

### Layer 2: the Goldreich–Levin theorem

- Proposition 8.12 (a predictor correct on every input yields an inverter), Proposition 8.13 with
  Claims 8.14 and 8.15 (success `3/4 + 1/p(n)`), and Proposition 8.16 with Claim 8.17 (success
  `1/2 + 1/p(n)`, by pairwise-independent sampling and majority decoding).
- Theorem 8.11 (the inner product `⟨x, r⟩` is a hard-core predicate of `g(x, r) = (f(x), r)` for
  every one-way function `f`), and Theorem 8.5 (every one-way function has a hard-core predicate
  after this modification).

### Layer 3: pseudorandom generators

- Definition 8.30, pseudorandom generators as indistinguishable ensembles, agreeing with
  Definition 3.14.
- Theorem 8.6 (a one-way permutation and a hard-core predicate give a one-bit-stretch PRG).
- Theorems 8.18 and 8.19, with Theorem 8.7 (any polynomial expansion from one bit of stretch).

### Layer 4: pseudorandom functions and permutations (the summit)

- Construction 8.20 with Theorem 8.21 (the GGM tree construction), giving Theorem 8.8
  (pseudorandom functions from length-doubling generators).
- Theorem 8.22 (the three-round Feistel network of a PRF is a pseudorandom permutation), and
  Construction 8.23 with Theorem 8.24 (four rounds give a strong pseudorandom permutation),
  giving Theorem 8.9.
- Corollary 8.10 (one-way permutations yield PRGs of every polynomial expansion, length-preserving
  PRFs, strong PRPs, authenticated encryption and secure MACs), using
  [PrivateKeyEncryption](../PrivateKeyEncryption/README.md), Layers 3–5.
- Proposition 8.27 (a pseudorandom generator yields a one-way function) and Proposition 8.28
  (EAV-secure encryption of `2n`-bit messages with `n`-bit keys yields a one-way function).

Theorems 8.25 and 8.26, which assume only a one-way *function*, rest on the theorem of Håstad,
Impagliazzo, Levin and Luby that one-way functions yield pseudorandom generators. KL3 cites that
theorem without proof, and it is not part of this roadmap.

## Worked examples (acceptance criteria)

- For the identity function, the inner-product predicate is not hard-core: Theorem 8.11 needs
  one-wayness.
- If `f` is a one-way permutation, so is `g(x, r) = (f(x), r)`.
- The two-round Feistel network is not a pseudorandom permutation: a two-query distinguisher
  succeeds with probability `1 - 2⁻ⁿ`.
- The GGM function on inputs of length one is the length-doubling generator itself.

## Ordering

Layer 0 starts immediately; Layer 1 needs Layer 0. The averaging claims of Layer 2 (8.14, 8.17)
need only Mathlib and start at once; the rest of Layer 2 needs Layer 1. Layer 3 needs Layer 2 and
[PrivateKeyEncryption](../PrivateKeyEncryption/README.md), Layer 2. Layer 4 needs Layer 3 and
PrivateKeyEncryption, Layers 3–5.

## Existing formalizations

- **Complexitylib** ([cslib-community/complexitylib](https://github.com/cslib-community/complexitylib),
  Apache 2.0) proves most of this roadmap on CSLib-style foundations: PPT machines and oracle
  composition
  ([`Computability/Probabilistic/PPT.lean`](https://github.com/cslib-community/complexitylib/blob/3e54050f944f13592e75ccc68135d045f73e0e11/Complexity/Computability/Probabilistic/PPT.lean)
  and the `ppt` tactic), Goldreich–Levin
  ([`Crypto/Computational/GoldreichLevin/HardCore.lean`](https://github.com/cslib-community/complexitylib/blob/3e54050f944f13592e75ccc68135d045f73e0e11/Complexity/Crypto/Computational/GoldreichLevin/HardCore.lean)),
  one-way functions to PRGs and polynomial stretch
  ([`OneWayToPRG.lean`](https://github.com/cslib-community/complexitylib/blob/3e54050f944f13592e75ccc68135d045f73e0e11/Complexity/Crypto/Computational/OneWayToPRG.lean),
  [`Stretch.lean`](https://github.com/cslib-community/complexitylib/blob/3e54050f944f13592e75ccc68135d045f73e0e11/Complexity/Crypto/Computational/Stretch.lean)),
  and GGM
  ([`GGM/Security.lean`](https://github.com/cslib-community/complexitylib/blob/3e54050f944f13592e75ccc68135d045f73e0e11/Complexity/Crypto/Computational/GGM/Security.lean)).
  Integrating it is coordinated with its author; this roadmap specifies the mathematics, not that
  code.
- **Katz–Lindell corpus** ([karnseth/katz-lindell](https://github.com/karnseth/katz-lindell),
  Apache 2.0): source-linked statements for Chapter 8, using an attributed copy of
  Complexitylib's machine core.

## References

- [KL3] J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd edition, CRC Press, 2021.
- O. Goldreich, L. A. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
- O. Goldreich, S. Goldwasser, S. Micali, *How to construct random functions*, J. ACM 33(4), 1986.
- M. Luby, C. Rackoff, *How to construct pseudorandom permutations from pseudorandom functions*,
  SIAM J. Comput. 17(2), 1988.

## Acknowledgements

Karn Seth's Katz–Lindell corpus provides the item inventory this roadmap follows, and
Complexitylib supplies the reference proofs.
