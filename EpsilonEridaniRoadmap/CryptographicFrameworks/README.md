# Cryptographic frameworks: games, reductions, and composable protocols

Build a reusable library for proving the security of cryptographic schemes and
protocols: probabilistic programs, efficient adversaries, security games and
their reductions, idealized oracle models, simulation-based and composable
security, and the standard constructions that exercise them. The endpoints
include the Fujisaki–Okamoto transform with decryption failures, Fiat–Shamir
signatures through the forking lemma, Yao's protocol from garbling and
oblivious transfer through sequential composition, the universal composition
theorem, and ML-KEM's chosen-ciphertext security from Module-LWE.

The aim is that a new paper from CRYPTO, EUROCRYPT, ASIACRYPT, TCC, CCS, or
IEEE S&P can be formalized as a short development on top of this library,
reusing its games, hybrids, oracles, simulators, and composition theorems
rather than rebuilding them. Individual papers and textbook chapters are later
roadmap areas that consume this one; they are listed at the end and are not
milestones here.

Cryptographic hardness assumptions (one-wayness, DDH, LWE, and so on) appear
only as explicit hypotheses with named advantage functions, never as axioms.
No milestone assumes a separation of complexity classes.

## Existing libraries and related work

Build on CSLib's [`Crypto`](https://github.com/leanprover/cslib/tree/main/Cslib/Crypto)
directory: [`Negligible`](https://github.com/leanprover/cslib/blob/main/Cslib/Crypto/Negligible.lean),
the PMF-based [`PRG`](https://github.com/leanprover/cslib/tree/main/Cslib/Crypto/Primitives/PRG)
games, [`Commitment`](https://github.com/leanprover/cslib/tree/main/Cslib/Crypto/Protocols/Commitment),
[`PerfectSecrecy`](https://github.com/leanprover/cslib/tree/main/Cslib/Crypto/Protocols/PerfectSecrecy),
and [`SecretSharing/Shamir`](https://github.com/leanprover/cslib/tree/main/Cslib/Crypto/Protocols/SecretSharing).
Use CSLib's [`Probability/PMF`](https://github.com/leanprover/cslib/blob/main/Cslib/Probability/PMF.lean)
and [`StatisticalDistance`](https://github.com/leanprover/cslib/blob/main/Cslib/Probability/StatisticalDistance.lean),
its `FreeM` oracle programs and query counters, its multitape machines and
polynomial bounds, and Mathlib's finite groups, `ZMod`, polynomial rings,
matrices, and probability.

The open CSLib pull requests on security games
([#1069](https://github.com/leanprover/cslib/pull/1069)), hybrid arguments with
polynomially many hops ([#1070](https://github.com/leanprover/cslib/pull/1070)),
PRG seeds and ideal distributions ([#1071](https://github.com/leanprover/cslib/pull/1071)),
games versus statistical distance ([#1072](https://github.com/leanprover/cslib/pull/1072)),
PMF normalization ([#1062](https://github.com/leanprover/cslib/pull/1062)),
statistical distance on arbitrary types ([#1065](https://github.com/leanprover/cslib/pull/1065)),
and probabilistic computations ([#1129](https://github.com/leanprover/cslib/pull/1129))
overlap M01–M04. Follow their resulting API decisions; the targets below are
the missing theory and connections. The earlier Katz–Lindell roadmap proposal
(this repository's PR #5: private-key encryption and one-way functions) is
complementary: its chapter-level targets should consume M01–M07.

[`complexitylib`](https://github.com/cslib-community/complexitylib) already
develops uniform polynomial-time machines, probabilistic computations, and
several cryptographic primitives and reductions (`Complexity/Crypto/`). The
foundational milestones M01–M05 are scoped so they can either consume
`complexitylib` as a dependency or be upstreamed into CSLib as the shared core
settles. Two other Lean 4 projects outside CSLib cover nearby ground and should
inform interface choices: [VCV-io](https://github.com/Verified-zkEVM/VCV-io)
(oracle computations and the forking lemma) and
[ArkLib](https://github.com/Verified-zkEVM/ArkLib) (interactive oracle proofs
and SNARKs). Port definitions with attribution where useful; do not add them
as dependencies. EasyCrypt, CryptHOL, and SSProve are design references for
game-based and package-based proofs.

## Conventions and acceptance criteria

- **Concrete security first.** Every security theorem constructs an explicit
  reduction `B` from the adversary `A` (as an oracle program or machine built
  from `A`) and states a concrete bound of the form
  `Adv_Π(A) ≤ c · Adv_Σ(B) + ε(λ, q)`, together with `B`'s running time and
  query counts in terms of `A`'s. Asymptotic security is a corollary. A bare
  `∃ B` with no construction, cost, or loss does not discharge a target.
- **Efficiency is a property of machines.** Polynomial time and PPT refer to
  CSLib machines, or to an operation-count model with a proved simulation
  bridge to them (M02). An arbitrary `Admissible` predicate supplied by the
  caller is permitted in intermediate statements, but each milestone's main
  theorems must instantiate it with the efficient-adversary class and prove
  that the reduction stays in that class. Adversaries are uniform unless a
  milestone explicitly says otherwise.
- **Sampling.** Specification games may sample uniformly from any nonempty
  finite type. Executable algorithms that only have fair coins sample `ZMod q`
  for non-power-of-two `q` by bounded rejection, with a proved statistical
  distance bound of the form `T · 2^(-σ)` between the ideal and executable
  games after `T` samples, and that bound is carried into the theorem.
- **No unspecified conditions.** A scheme, assumption, or functionality is a
  concrete structure: algorithms with stated types, and security conditions
  stated as games. An arbitrary `Prop` field standing in for "is secure" or
  "is efficient" does not specify the requirement.
- **Non-vacuity and load-bearing hypotheses.** Every positive security theorem
  has a small concrete instance showing its hypotheses are simultaneously
  satisfiable. Where the literature identifies a hypothesis as necessary
  (correlation robustness for Free-XOR, injectivity or γ-spreadness in the FO
  transform, public inputs in the Fiat–Shamir hash, consistency checks in OT
  extension), prove an explicit attack on the variant that drops it.
- **Usable objects.** New definitions come with extensionality, the effect of
  relabelling and renaming, boundary cases, and the composition lemmas later
  milestones need. A reduction comes with correctness, construction, cost, and
  its effect on each advantage and resource parameter.

## Milestones

Dependencies name prerequisite milestones, in addition to existing upstream
APIs. Each milestone can be implemented in smaller contributions along its
listed theorem boundaries.

### M01. Probabilistic programs and distances

Extend CSLib PMFs with the algorithm-facing toolkit: `bind`/`map` laws,
product and independent sampling, conditioning on events of positive
probability, statistical distance with the data-processing inequality, the
triangle inequality, the coupling characterization, and the bound for `T`
independent samples. Prove the bounded-rejection sampler for `ZMod q`: its
output distance from uniform, its expected and capped coin usage, and the
replacement lemma that swaps it for the ideal sampler inside any game at the
stated cost. Relate PMF programs to `FreeM` programs over a coin oracle.

### M02. Efficient adversaries and oracle machines

Dependencies: M01.

Define probabilistic oracle algorithms with explicit time, coin, and query
budgets, and the efficient-adversary class as polynomial budgets in the
security parameter. Prove closure under sequential composition, polynomially
bounded iteration, and oracle substitution (replacing an oracle by an
efficient implementation gives an efficient algorithm with the composed
budget). Give the simulation bridge between the operation-count model and
CSLib's multitape machines, with its exact overhead. Polynomial overhead
preserves efficiency; it need not preserve a concrete running time.

### M03. Security games, advantage, and negligibility

Dependencies: M02.

On top of the CSLib game API, define winning games and distinguishing games,
their advantages, and the relations between them (guessing-bit advantage
versus two-world distinguishing advantage, with the factor of two). Define
concrete security `(t, q, ε)` and asymptotic security over the efficient class
from M02, and prove that concrete bounds with polynomial loss imply asymptotic
security. Give computational indistinguishability of ensembles and its
closure under efficient post-processing.

### M04. Game hopping and hybrid arguments

Dependencies: M03.

Prove the fundamental lemma of game playing: for games identical until a bad
event, the difference in any event's probability is at most the probability of
the bad event. Give the indexed hybrid argument for polynomially many hops,
with the reduction that guesses the hop index and its `1/k` loss. Provide
reduction combinators that compose losses and resource bounds. Optionally,
supply a package interface in the style of state-separating proofs
(sequential and parallel composition, associativity, and the reduction lemma);
if provided, prove it agrees with the plain game interface on the examples in
M08.

### M05. Oracles and idealized models

Dependencies: M02, M04.

Define stateful oracles with query logs and counters. Prove that lazily and
eagerly sampled random functions give identical games, and that programming a
random oracle at a point not previously queried is undetectable, with the
bound for points chosen with min-entropy `k`. Prove the birthday collision
bound for `q` queries to a random function and the PRP/PRF switching lemma.
State the ideal cipher model with its lazy-permutation implementation. All
idealized models are explicit oracles given to every party; none is an axiom
about a concrete hash function.

### M06. Rewinding and the forking lemma

Dependencies: M05.

Prove the general forking lemma: for an algorithm making at most `q` queries
to a hash with range of size `h` and accepting with probability `acc`, the
forking algorithm succeeds with probability at least `acc · (acc/q − 1/h)`.
Construct the forking algorithm explicitly, with its running time (two runs
plus bookkeeping) and coin usage. Prove the special-soundness extraction
corollary for Σ-protocols that M10 uses.

### M07. Assumptions and their reductions

Dependencies: M03, M04.

Define, as games with named advantages: one-way functions and permutations,
hard-core predicates, PRGs, PRFs, and pseudorandom permutations; discrete
logarithm, CDH, and DDH over a finite cyclic group given by an explicit
generator and order; and LWE, SIS, and LPN with explicit dimension, modulus,
sample count, and error distribution. Prove the reductions DDH ⇒ CDH ⇒ DLog,
random self-reducibility of DLog and DDH, length extension of PRGs by the
hybrid argument, and the Goldreich–Goldwasser–Micali PRF from a length-doubling
PRG with its `q · n` loss. Prove the LWE normal form (secret from the error
distribution) and decision-to-search for prime polynomial modulus. Assumptions
are definitions and implications with hypotheses, never asserted true.

### M08. Symmetric encryption, MACs, and authenticated encryption

Dependencies: M05, M07.

Define IND-CPA, IND-CCA, EUF-CMA for MACs, and INT-CTXT. Prove CPA security of
randomized counter-mode encryption from a PRF, EUF-CMA of the PRF MAC, and the
encrypt-then-MAC composition theorem giving IND-CCA and INT-CTXT, with concrete
bounds. Include the attack showing that MAC-then-encrypt with a malleable
cipher need not be CCA-secure. This milestone fixes the generic syntax; the
textbook catalogue of modes belongs to the Katz–Lindell area.

### M09. Public-key encryption, KEMs, and the Fujisaki–Okamoto transform

Dependencies: M05, M07, M08.

Define PKE and KEM syntax, correctness error `δ`, γ-spreadness, OW-CPA,
IND-CPA, and IND-CCA. Prove ElGamal IND-CPA from DDH, Regev encryption IND-CPA
from decision LWE with its correctness bound, and the KEM/DEM composition
theorem. Formalize the modular Fujisaki–Okamoto transform of
Hofheinz–Hövelmanns–Kiltz: `T` (OW-CPA to OW-PCA in the random oracle model)
and `U^⊥` and `U^⊥̸` (to IND-CCA), with the stated bounds including the `δ`
and `γ` terms. Give the attack on a variant without the spreadness or
re-encryption check. Only the classical random oracle model is in scope.

### M10. Σ-protocols, Fiat–Shamir, and signatures

Dependencies: M06, M07.

Define Σ-protocols with completeness, special soundness, and special
honest-verifier zero knowledge, and prove AND and OR composition. Instantiate
Schnorr's protocol over a cyclic group. Define EUF-CMA signatures and prove
that Fiat–Shamir applied to a Σ-protocol with a hard relation and high
min-entropy commitments gives an EUF-CMA signature in the random oracle model,
via M06, with the concrete bound. Prove the attack in which omitting the
statement from the hash allows forgeries for adaptively chosen statements.
State Fiat–Shamir with aborts (rejection sampling with explicit acceptance
probability) as the interface that M15 consumes.

### M11. Commitments and verifiable secret sharing

Dependencies: M07.

Extend CSLib's commitment and Shamir developments: Pedersen commitments
(perfectly hiding, computationally binding under DLog), hash-based commitments
in the random oracle model, and Feldman verifiable secret sharing with
correctness and the DLog-based secrecy statement. Prove that Shamir sharing
over `ZMod p` reconstructs from any `t + 1` shares and reveals nothing to any
`t`, connecting to the existing CSLib statements rather than restating them.

### M12. Simulation-based security for two-party protocols

Dependencies: M03, M04.

Define two-party functionalities, protocols as interactive oracle programs,
views, and semi-honest security by the existence of an explicit efficient
simulator whose output is indistinguishable from the real view together with
the output. Define malicious security with abort. Prove the sequential modular
composition theorem: replacing ideal calls by secure protocols preserves
security, with the composed simulator and bound. Include the deterministic
functionality simplification and its failure for randomized functionalities.

### M13. Oblivious transfer and the GMW protocol

Dependencies: M07, M12.

Prove semi-honest security of an OT protocol from DDH, and of
Ishai–Kilian–Nissim–Petrank OT extension from `κ` base OTs and a
correlation-robust hash, with the concrete bound. Prove the selective-failure
attack on the malicious-receiver variant without a consistency check. Prove
semi-honest security of two-party GMW for Boolean circuits in the OT-hybrid
model, using M12's composition theorem.

### M14. Garbled circuits

Dependencies: M05, M12, M13.

Formalize the garbling-scheme framework of Bellare–Hoang–Rogaway: syntax,
correctness, and the privacy, obliviousness, and authenticity notions in both
indistinguishability and simulation form, with their equivalence for
efficiently invertible side-information functions. Prove privacy of Yao's
garbling with point-and-permute from a dual-key cipher, Free-XOR under circular
correlation robustness, and half-gates (Zahur–Rosulek–Evans) with its two
ciphertexts per AND gate. Prove the attack on Free-XOR under plain correlation
robustness where the literature requires the circular notion. Deduce
semi-honest security of Yao's two-party protocol from garbling and OT via M12.

### M15. Module lattices and the standardized schemes

Dependencies: M07, M09, M10.

Define the ring `R_q = ZMod q[X]/(X^n + 1)` for power-of-two `n`, centered
reduction, infinity norms, and Ring- and Module-LWE as instances of M07's
interface with the embedding into LWE. Prove correctness of the K-PKE scheme
underlying ML-KEM with an explicit failure bound as a function of the
parameters, its IND-CPA security from Module-LWE, and ML-KEM's IND-CCA security
by instantiating M09's transform. State ML-DSA's EUF-CMA security through
M10's Fiat–Shamir-with-aborts interface under Module-LWE and Module-SIS.
Follow FIPS 203 and FIPS 204 for algorithms; numerical security estimates are
outside scope.

### M16. Universal composability

Dependencies: M02, M12.

Define interactive machines with identities and session identifiers, an
execution model with explicit polynomial activation budgets for the
environment, and real and ideal executions. Prove that the dummy adversary is
complete, and prove the universal composition theorem for a single
subroutine and for polynomially many sessions, with the composed simulator
and bound. Define `F_COM` and `F_CRS`, prove the Canetti–Fischlin
impossibility of UC commitments in the plain model for two parties, and prove
a UC commitment in the `F_CRS`-hybrid model. Prove that UC security implies
the standalone security of M12. Global and joint-state composition are later
targets.

## Dependency and launch order

The dependency graph is the milestone dependency lists above. An order
satisfying all dependencies is:

1. M01–M05: distributions, efficient adversaries, games, hybrids, and oracles.
   These consume and extend the open CSLib PRs and are useful on their own.
2. M06–M09, M11, M12: forking, the assumption library, symmetric and
   public-key encryption, commitments, and simulation-based security.
3. M10, M13–M16: Fiat–Shamir, OT and GMW, garbling, module lattices, and UC.

Start implementation with M01 and M04's fundamental lemma, then M05's
lazy/eager equivalence; together with the CSLib PRs they unblock every other
milestone.

Completion means the definitions, explicit reductions, simulators, concrete
bounds, efficiency proofs, non-vacuity instances, and attacks above are
implemented against existing APIs. Definitions alone, statements with
unconstructed reductions, or theorems quantified over an unspecified
`Admissible` class do not discharge a milestone.

## Follow-up areas (not milestones here)

Each of these is intended as its own roadmap area consuming this one:
correlated randomness and silent protocols (VOLE, pseudorandom correlation
generators, PSI); recent garbling results (arithmetic garbling, stacked
garbling, garbling lower bounds); post-quantum schemes beyond lattices
(code-based KEMs, hash-based and multivariate signatures, MPC-in-the-head);
quantum random oracles and post-quantum rewinding; zero-knowledge proofs and
SNARKs, coordinated with ArkLib; pairings and the algebraic group model;
provable symmetric modes and key-committing AEAD; fully homomorphic
encryption; threshold signatures; and chapter-by-chapter coverage of
Katz–Lindell, Boneh–Shoup, and Goldreich.

## References

These specify classical results and conventions. They do not prescribe a
file-by-file port of an existing formalization.

- **Textbooks:** Katz–Lindell, *Introduction to Modern Cryptography*, 3rd ed.;
  Boneh–Shoup, [*A Graduate Course in Applied Cryptography*](https://toc.cryptobook.us/);
  Goldreich, *Foundations of Cryptography*, Vols. 1–2.
- **Games and hybrids (M03–M05):** Shoup, [*Sequences of Games*](https://eprint.iacr.org/2004/332);
  Bellare–Rogaway, [*Code-Based Game-Playing Proofs*](https://eprint.iacr.org/2004/331);
  Brzuska et al., [*State-Separating Proofs*](https://eprint.iacr.org/2018/306).
- **Forking lemma (M06):** Pointcheval–Stern, *Security Arguments for Digital
  Signatures and Blind Signatures*; Bellare–Neven, *Multi-Signatures in the
  Plain Public-Key Model and a General Forking Lemma* (CCS 2006).
- **Fujisaki–Okamoto (M09):** Hofheinz–Hövelmanns–Kiltz,
  [*A Modular Analysis of the Fujisaki-Okamoto Transformation*](https://eprint.iacr.org/2017/604).
- **Simulation (M12):** Lindell, [*How to Simulate It*](https://eprint.iacr.org/2016/046).
- **OT extension (M13):** Ishai–Kilian–Nissim–Petrank, *Extending Oblivious
  Transfers Efficiently* (CRYPTO 2003).
- **Garbling (M14):** Bellare–Hoang–Rogaway, [*Foundations of Garbled Circuits*](https://eprint.iacr.org/2012/265);
  Kolesnikov–Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications* (ICALP 2008); Zahur–Rosulek–Evans, [*Two Halves Make a Whole*](https://eprint.iacr.org/2014/756).
- **Lattices (M07, M15):** Regev, *On Lattices, Learning with Errors, Random
  Linear Codes, and Cryptography* (STOC 2005); [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final)
  and [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final).
- **Universal composability (M16):** Canetti, [*Universally Composable Security*](https://eprint.iacr.org/2000/067);
  Canetti–Fischlin, *Universally Composable Commitments* (CRYPTO 2001).
