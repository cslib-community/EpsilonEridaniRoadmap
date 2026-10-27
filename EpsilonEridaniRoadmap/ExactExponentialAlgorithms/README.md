# SAT, exact exponential algorithms, and their neighbourhood

Build a reusable library of Boolean satisfiability, exact counting, exponential
algorithms, size-sensitive reductions, and the classical algebraic and
pseudorandom tools that connect them. The endpoints include Cook–Levin,
parsimonious counting completeness, disjoint sparsification, standard SAT
algorithms, conditional fine-grained lower bounds, and the classical connection
between faster exhaustive search and circuit lower bounds.

The scope is the established theory surrounding ETH. The announced ETH
refutation, its new algorithm, its special replacement-form and shared-summary
constructions, its new tensor-contraction bound, and its sharper circuit lower
bound are outside this roadmap. No milestone assumes that result. Statements
about ETH, SETH, or #ETH are definitions and implications with explicit
hypotheses, never axioms declaring those hypotheses true.

Only missing extensions are implementation targets. Reuse an upstream result
when it becomes available, and retain the bridges to the rest of this roadmap.

## Existing libraries and related work

Use Lean's [`Std.Sat.CNF`](https://github.com/leanprover/lean4/tree/v4.36.0-rc1/src/Std/Sat/CNF)
and [`AIG.CNF`](https://github.com/leanprover/lean4/blob/v4.36.0-rc1/src/Std/Sat/AIG/CNF.lean)
for existing syntax, semantics and equisatisfiability results. Build on CSLib's
[`Circuit`](https://github.com/leanprover/cslib/tree/main/Cslib/Computability/Circuit)
and [`MultiTape`](https://github.com/leanprover/cslib/tree/main/Cslib/Computability/Machines/Turing/MultiTape)
APIs, polynomial bounds and `TimeM`; extend Mathlib's polynomials, interpolation,
finite Fourier theory, matrices, graphs and probability estimates.

The [CSLib complexity plan](https://github.com/leanprover/cslib/issues/611),
[complexity-class proposal](https://github.com/leanprover/cslib/pull/192),
[encoding proposal](https://github.com/leanprover/cslib/pull/591), and
[coding-theory proposal](https://github.com/leanprover/cslib/pull/844) overlap
the foundations here. Follow their resulting API decisions and provide the
equivalence and resource bridges required below. Existing components discharge
the corresponding parts of a milestone; the targets are their missing theory
and connections.

## Conventions and acceptance criteria

- Use `Std.Sat.CNF (Fin n)` and its clause, literal, evaluation, and relabelling
  APIs. The input includes the number `n` of **declared** variables, including
  unused ones. An assignment is `Fin n → Bool`. Clause width is at most `k`;
  shorter clauses, including the empty clause, are permitted. Keep clause
  multiplicities in input data, especially for optimisation and weights.
- Write `n`, `m`, `ell`, and `L` for declared variables, input clauses, literal
  occurrences, and encoded input bits. Counts include all declared variables.
  Define `#F` as the cardinality of the finite set of satisfying assignments.
  Boolean literal polarity follows Std's evaluation convention.
- Use an injective, decodable binary encoding of the input syntax. Encode `n`
  in unary and literal indices in binary, with unambiguous framing. Require
  `n ≤ L` and `L = O(n + m + ell * log₂(n + 2) + 1)`. Syntax normalisation is a
  proved transformation, not part of an allegedly injective encoding of
  unnormalised syntax. Declare the output encoding of integers as binary.
- Resource theorems use CSLib's finite-state, binary, multitape machines and
  `Turing.ComputableInTimeAndSpace` or the corresponding decision predicate.
  Follow its existing input/output/work-tape conventions. If an application
  needs total visited space, prove the comparison including input and output.
  Abstract operation counts may be intermediate theorems; machine bounds also
  require implementation and simulation proofs. `TimeM` annotations alone do
  not establish bit complexity.
- `O*` suppresses polynomial factors in `L`, not arbitrary functions of `n` or
  the parameter. `O_k` permits dependence on fixed width `k`, and no dependence
  on `n,m,L`. Algorithms and constants are quantified before their inputs.
  Distinguish deterministic worst-case, bounded-error, and expected bounds.
- Every new object needs extensionality, renaming, boundary cases, and the
  basic closure/interaction lemmas that make it usable. A reduction needs
  correctness, a construction algorithm, its cost, and its effect on each
  relevant size parameter. A counting reduction needs a proved fibre count or
  a bijection, rather than just equisatisfiability.

## Milestones

Dependencies name prerequisite milestones, in addition to existing upstream
APIs. Each milestone can be implemented in smaller contributions along its
listed theorem boundaries.

### M01. Finite SAT and counting semantics

Extend Std's CNF semantics with satisfying-assignment finsets, counts, bounded
width, occurrence counts, support, partial assignments, and restriction. Prove:

1. `#F > 0` iff `F` is satisfiable; `0 ≤ #F ≤ 2^n`; the empty conjunction has
   count `2^n`, and a formula containing an empty clause has count zero.
2. Bijective variable renaming preserves counts. Adding `r` unused declared
   variables multiplies the count by `2^r`; removing unused variables has the
   corresponding factor, rather than silently preserving the count.
3. Restriction has a bijection between satisfying extensions and residual
   assignments. In particular, branching on a variable partitions solutions
   into its false and true restrictions, so the counts add.
4. Duplicate literal deletion, duplicate clause deletion, tautology deletion,
   subsumption, and unit propagation preserve their stated solution sets or
   have explicit extension maps. Prove occurrence/width effects separately.

Connect CNF evaluation to CSLib's existing propositional language and Boolean
circuits without introducing another general propositional syntax.

### M02. Encodings and sizes

Dependencies: M01.

Construct the encoding fixed above, its decoder, round-trip/injectivity proofs,
and bounds for parsing, evaluation, restriction, renaming, and normalisation.
Malformed bitstrings must have a specified rejection behaviour when a language
is defined on all words. Establish binary count-output length at most `n + 1`.
Give size bounds before and after literal/clause deduplication; for fixed `k`,
the number of distinct width-at-most-`k` clauses is polynomial in `n`.

Relate this encoding to Std's DIMACS support and to upstream encoding APIs.
Separate semantic interoperability from an efficient encoding conversion:
an arbitrary `Encodable` instance does not imply either a size or time bound.

### M03. Resource-aware programming and arithmetic

Dependencies: M02.

Extend the existing multitape combinators with the operations used below:
binary counters, comparison, addition, multiplication, exact division, gcd,
framed sequences, finite enumeration, bounded loops, sequential composition,
and depth-first traversal with reusable workspace. Prove implementations and
polynomial bit bounds for integer and rational arithmetic on bounded-length
operands, using ordinary schoolbook algorithms where sufficient. Include
numerator/denominator growth bounds and exact recovery of an integral rational
answer. Exponential running time must not be used as a polynomial-space bound.

Provide compositional cost lemmas for these operations and their use in
`TimeM` analyses. For any additional execution language, supplying its
resource-preserving compiler is part of this milestone.

### M04. Reductions and resource transfer

Dependencies: M03.

Define polynomial-time many-one reductions, parsimonious reductions, and
oracle/Turing reductions with explicit query and answer lengths. Prove
identity, composition, and transfer of decision/function bounds. Include
reductions returning disjoint lists of instances whose answers are summed.

For parameter `p(x)`, give a separate size-sensitive interface recording
`p(f(x)) ≤ a*p(x)+b` and polynomial output length/construction cost. Prove that
it transports `2^{o(p)} poly(L)` bounds. Prove corresponding bounds for a list
of at most `2^{epsilon*p}` outputs processed sequentially, including accumulated
time and maximum live workspace. Model simulations must state their exact
overhead: polynomial time overhead preserves subexponentiality, but need not
preserve an exponential base or a fine-grained polynomial saving. To transfer
polynomial space, bound simulator space in terms of input, simulated space,
and counters, rather than a polynomial in simulated running time.

### M05. Classical complexity and counting classes

Dependencies: M04.

Build on upstream class definitions, with equivalence bridges where machine
models differ. Supply `DTIME`, `NTIME`, `P`, `NP`, `coNP`, `FP`, `#P`, `E`,
`EXP`, and polynomial space at the generality needed here. Define NP and #P
through polynomial-time verifiers with **fixed polynomially bounded witness
length**, so padding does not inadvertently multiply counts. Prove the
nondeterministic-machine/verifier equivalence with a canonical encoding of
branch choices and accepting computations, explicitly handling branching
multiplicities for #P.

Prove standard inclusions, closure under the reductions in M04, finite-language
and polynomial-prefix conventions, SAT membership in NP, and #SAT membership
in #P. No separation conjecture is a target theorem.

### M06. Tseitin, Cook–Levin, and counting completeness

Dependencies: M05.

Connect CSLib's topologically ordered Boolean circuits to Std AIGs/CNF and
prove a fan-in-two circuit-to-width-three encoding with `O(n+g)` variables
and clauses for `n` inputs and `g` gates. For every fixed input assignment,
prove the **unique extension** of every gate value, and that requiring the
output to be true gives a bijection of satisfying assignments. Account for
unreachable gates and unused input variables; an equisatisfiability theorem
for a pruned AIG alone does not provide this bijection.

Give a uniform polynomial-size circuit/tableau simulation of a clocked
polynomial-time verifier, including its construction time. Deduce SAT and
3-SAT NP-completeness and #SAT and #3-SAT #P-completeness under parsimonious
reductions. Long-clause conversion for counting must use unique-extension
gadgets; the usual existence-only chain gadget is insufficient.

### M07. Baseline solvers and tractable fragments

Dependencies: M03, M06.

Implement exhaustive SAT/#SAT, DPLL with unit propagation, Horn-SAT by least
model propagation, and 2-SAT by implication-graph reachability. Build the
finite reachability algorithm and its cost proof as part of the 2-SAT target.
Prove soundness, completeness, termination, `O*(2^n)` time and polynomial space
for the baseline general solver, and polynomial bit time for Horn/2-SAT.
Show that the least Horn model need not be its only model. Counting
completeness for #2-SAT is a separate target in M13.

### M08. Branching and randomised exponential algorithms

Dependencies: M07, M19.

Develop search-tree recurrences and branching-vector bounds: for positive
decreases `(a_i)` and `r > 1`, the exponential bound is `r^n` when
`sum_i r^(-a_i) ≤ 1`, with
polynomial per-node overhead treated separately. Apply it to explicit SAT
branching rules, recording whether branches partition solutions or merely
cover them.

Formalise Schöning's random-walk algorithm for fixed `k ≥ 3`: couple progress
to the distance from a fixed satisfying assignment, prove the success bound
for a trial and independent restarts, and obtain bounded-error
`O*((2-2/k)^n)` time and polynomial space. Specify the random-bit model and
one-sided error. This is the classical algorithm, without a target of matching
the latest numerical SAT record. [Schöning](#references)

### M09. Decision, search, counting, and generation

Dependencies: M04, M07, M19.

Prove SAT search-to-decision by at most `n+1` oracle calls, and search and
exact sampling from exact conditional counts. For a satisfiable formula,
choosing each branch proportionally to its remaining count must produce the
uniform distribution on satisfying assignments. Implement exact rational
choices with fair bits using rejection sampling; bound expected overhead and
handle the zero-count case. State precisely the polynomial time overhead and
workspace for substituting an oracle implementation. Include threshold
optimisation by binary search with witness recovery.

This milestone proves reductions between tasks; it does not identify their
complexity classes or assert that a decision oracle counts solutions.
[Jerrum–Valiant–Vazirani](#references)

### M10. Sparsification and bounded occurrence

Dependencies: M04, M07, M08 (branching lemmas only).

Prove the sunflower lemma for finite bounded-size set families, with explicit
quantitative bounds, and its application to clause families. Prove the
disjoint/counting version of sparsification: for fixed `k` and rational
`epsilon > 0`, construct at most `2^{epsilon*n}` width-at-most-`k` formulas
on the **same declared variables**, whose satisfying-assignment sets partition
that of the input and whose variable occurrences are bounded by a computable
constant `C(k,epsilon)`. Include construction time
`2^{epsilon*n} poly_{k,epsilon}(L)` and a depth-first polynomial-space
implementation; the exponentially long output list need not be stored.

Publish explicit computable bounds for `C`, branching depth, and per-node
work before instantiating `epsilon` as a function of input size. Bounds with
unspecified epsilon-dependent constants cannot justify that substitution.

Supply parsimonious width reduction and variable-copying/equality gadgets,
with linear size in the occurrences and an explicit constant occurrence
bound for the resulting width-three formula. Track every auxiliary variable.
[Impagliazzo–Paturi–Zane; Dell et al.](#references)

### M11. Exponential rates and the hypothesis landscape

Dependencies: M05, M06, M10.

Define `s_k` as the infimum of positive `delta` for which a deterministic
fixed machine decides width-at-most-`k` SAT in `2^{delta*n} poly(L)` time.
Define the analogous counting rate. Define ETH by `s_3 > 0`, SETH by
`sup_{k ≥ 3} s_k = 1`, and #ETH by positivity of the counting rate at width
three. Give equivalent rate/algorithm-family formulations, handling infima
and finite prefixes explicitly.

Prove width monotonicity, exhaustive-search upper bounds, `SETH → ETH`,
`ETH → #ETH`, and the equivalence between variable and clause formulations
of ETH through sparsification. Distinguish the family
`∀ epsilon > 0, ∃ machine_epsilon` from a **single** machine with a
`2^{o(n)} poly(L)` bound. Prove implications in the valid direction, and
require effective uniformity hypotheses for any conversion back.

Define randomised and gap variants separately, with their error models;
prove only implications justified by explicit reductions. Unrestricted
CNF-SAT allows width to grow with the input, whereas SETH quantifies over
fixed widths. Add the elementary little-o/exponential closure lemmas needed
to check these distinctions, reusing Mathlib asymptotics and CSLib bounds.

### M12. Parameterised algorithms and tree decompositions

Dependencies: M04, M10, M11, M18.

Define parameterised problems, FPT, XP, and reductions recording both output
parameter and instance size. Prove their basic closure laws. Construct the
sparse-3-SAT-to-Clique reduction by grouping clauses, with `r` parts and
`r*2^{O(n/r)}` vertices, and prove the conditional theorem that ETH excludes
Clique time `f(r)*N^{o(r)}` for computable `f`.

Build finite graph tree decompositions, width, conversion to nice
decompositions, and bag-consistency lemmas on Mathlib graphs. For a supplied
decomposition of the primal graph of a domain-`q` CSP, implement decision
and counting in `q^{w+1} poly(L, decomposition size)` time. Include construction
of DP transitions, joins, projection, and the assignment-count invariant.
The decomposition is an input; finding an optimal decomposition is outside
this target. Do not infer an algorithm for every parameterised problem from
failure of a conditional lower-bound assumption.

### M13. Concrete counting and decision reductions

Dependencies: M06, M09, M16, M18.

Prove the following correspondences, reusing Mathlib's graph, colouring, and
matching objects. Each row needs an executable encoding and the indicated
assignment bijection, as well as construction and bit-length bounds.

| Source objects | Boolean encoding | Parameter to record |
| --- | --- | --- |
| Independent sets | One variable per vertex; `¬x_u ∨ ¬x_v` per edge | `n=v`, width two |
| Proper `q`-colourings, fixed `q≥2` | One-hot vertex colours and edge exclusions | `n=qv`, width at most `max(q,2)` |
| Perfect matchings | One bit per edge; a linear-size circuit checks exactly one incident selected edge | After Tseitin, `n=O(v+e)`, width three |
| Fixed-arity finite-domain CSP solutions | One-hot variables and clauses forbidding disallowed tuples | For fixed domain and arity, variables linear in source variables |
| Set splitting with sets of size at most `k` | Each set has both a positive and a negative clause | One variable per universe element; width at most `k` |
| Preimages of a Boolean map with constant output locality | Truth-table constraints for prescribed output bits | Input bits are the variables; fixed width |

For perfect matchings, construct a sequential exactly-one circuit with
`O(degree)` gates per vertex, rather than a quadratic pairwise construction.
For set splitting count ordered sides, not unordered bipartitions. For colourings
count labelled colours. Express runtime transfers **conditionally on a supplied
SAT/counting algorithm**, preserving the table's actual parameter; in
particular the matching bound is in `v+e`, not automatically `v`.

Prove #2-SAT #P-completeness under polynomial-time **counting Turing
reductions**, by supplying the reductions, interpolation, and fibre-count
identities. Parsimonious completeness is not requested: together with
polynomial-time 2-SAT it would imply `P=NP`.

### M14. Fine-grained reductions and Orthogonal Vectors

Dependencies: M04, M11.

Define fine-grained oracle reductions with a budget for the sum of query
costs; prove composition and transfer of a polynomial saving. Define the
bichromatic Boolean Orthogonal Vectors problem and its quadratic baseline.
Construct split-and-list from CNF-SAT: split the variables, encode each half
assignment by the clauses it leaves unsatisfied, and prove that orthogonality
is equivalent to a satisfying combined assignment. Record list sizes
`2^{ceil(n/2)}`, dimension `m`, and construction time.

Deduce `SETH → OVC` for the precise version asserting that there is no fixed
`delta > 0` algorithm with time `O(N^{2-delta} poly(d))`. State any more
restricted dimension version separately and supply its quantifiers and
sparsification argument. Prove the hypothetical OV-speedup-to-SAT-speedup
theorem directly. A SAT-to-OV reduction does not transport a fast SAT solver
back to OV. No implication from `¬SETH` to `¬OVC` is a target.

### M15. Boolean polynomials and subset transforms

Dependencies: M01; M03 for algorithms.

On Mathlib `MvPolynomial`, develop multilinear reduction modulo
`X_i^2-X_i`, evaluation on the Boolean cube, and uniqueness of the multilinear
representative over a field. Prove the finite Möbius-inversion coefficient
formula and sum–product factorisation on disjoint variable sets. Translate
clauses into Boolean indicator polynomials with proved degree and coefficient
bounds. Relate the sum of the product of clause indicators to `#F`.

Develop subset zeta/Möbius transforms and inclusion–exclusion as algorithms,
with `O(n*2^n)` ring operations and their actual storage bounds. Give a
separate polynomial-space direct enumeration. Over characteristic zero,
include Boolean Fourier characters, orthogonality, inversion, Parseval, and
Walsh–Hadamard transform, using Mathlib's finite abelian Fourier APIs. Do not
assert the Fourier statements over fields of characteristic two.

### M16. Interpolation and truncated algebra

Dependencies: M15; M03 for bit bounds.

Extend Mathlib's Lagrange interpolation, Taylor and Hasse-derivative APIs with
the missing effective results: Hermite interpolation at distinct nodes with
multiplicities, uniqueness below total multiplicity, reconstruction of a
specified value from Taylor coefficients, and algorithms over the rationals
and finite fields under the appropriate characteristic hypotheses. Hasse
coefficients avoid silently dividing by a zero factorial.

Supply computation in `R[T]/(T^r)` through a proved truncated-polynomial
representation, including multiplication, coefficient extraction and substitution
by polynomials with zero constant coefficient. Prove compatibility of truncation
with finite sums/products and low coefficients of Taylor expansions; evaluation
at a nonzero point is not an operation on this quotient. Prove degree, coefficient-height,
denominator, time, and workspace bounds for reconstruction from bounded-size
data. The target is ordinary interpolation; the announced paper's specialised
precision/recovery lemma is excluded.

### M17. Effective linear algebra and structured matrices

Dependencies: M03, M15, M16.

Reuse Mathlib matrices, rank, kernels and Kronecker products. Add algorithms
for exact rational elimination, rank, kernel bases, and selecting independent
rows, with correctness and polynomial bit complexity, for example by
fraction-free elimination and determinant bounds.

Develop Boolean-cube character matrices, group-circulant matrices and
Kronecker powers: eigenvectors/eigenvalues from finite characters, rank from
nonzero eigenvalues over a splitting field, and change-of-scalars lemmas.
For a rational matrix, select a row-space basis from its rows; if its entries
are in `{-1,0,1}`, prove that `r` selected measurements on an `n`-bit vector
have at most `(2n+1)^r` possible values. Prove fibre partition and summation
identities for arbitrary linear measurements. These are generic facts, with
no target of constructing the new low-rank matrices from the ETH paper.

### M18. Weighted CSPs and tensor networks

Dependencies: M01, M03, M15, M16.

Define finite-domain, finite-scope weighted constraints and partition functions
over a commutative semiring, with zero/one constraints recovering ordinary
solution counts. Give renaming, conditioning, disjoint-union, and variable
elimination theorems. Relate tensors to finite arrays and prove contraction
equals the corresponding sum of products, including repeated incidences,
isolated variables, empty scopes and disconnected networks.

Implement elementary contraction/elimination in a supplied order. Bound
operations by the actual intermediate scopes, and memory by the actual live
tables. Prove that conditioning on a separator makes component partition
functions multiply and that summing separator values recovers the original.
Support integer, rational, finite-field and truncated-polynomial weights
with their own bit/representation costs. No general subexponential contraction
algorithm is requested.

### M19. Finite probability and derandomisation tools

Dependencies: M03.

Build on CSLib PMFs and Mathlib finite probability and subgaussian estimates.
Supply algorithm-facing statements of independent product sampling, union
bounds, Chernoff/Hoeffding bounds for bounded variables, and amplification.
Include exact fair-bit sampling of bounded integers, expected rejection cost,
and a capped version with quantified failure probability. Prove the method
of conditional expectations for a finite product space, with a deterministic
algorithm when conditional expectations are exactly computable. Include the
cost of obtaining those expectations instead of treating them as free.

### M20. Small bias, expanders, and parity-check codes

Dependencies: M17, M19.

For `(ZMod 2)^r`, define epsilon-biased multisets by their nontrivial character
averages. For rational `0 < epsilon < 1`, prove existence with multiset size
at most `ceil(4*(r+1)/epsilon^2)`, an effective exhaustive construction with
explicit search cost, and the resulting eigenvalue bound
for the associated Cayley multigraph and bipartite double cover. Repeated
edges must retain multiplicity. Prove the spectral-to-edge-expansion estimate
with its hypotheses. No polynomial-time search bound follows just from
existence or decidability of the property. [Naor–Naor](#references)

Extend upstream finite-code APIs with binary linear codes, parity-check
matrices, rate, minimum distance, restriction/shortening, and Tanner codes.
Prove that local code distance together with a specified expansion inequality
forces a global distance bound. In particular, for a `d`-regular bipartite
graph with `N` vertices on each side, normalised nontrivial singular-value
bound `lambda`, and local relative distance `delta > lambda`, prove global
relative distance at least `delta*(delta-lambda)` among its `d*N` edge bits.
Construct finite local codes by the stated search method, with certified
distance and cost. Use these codes as parity tests on Boolean vectors; prove
that a nonzero vector satisfying all checks has the resulting minimum
support. This is the classical coding argument, without the new SAT-specific
parameter balancing or test-selection algorithm. [Sipser–Spielman](#references)

### M21. Optimisation and sampling of constraints

Dependencies: M06, M09, M19.

Define Max-k-SAT with clause multiplicity and the finite-domain Max-CSP
analogue. Prove uniform approximation of all assignment scores by a random
sample of constraints: for `s` independent uniform samples, error exceeding
`delta` for some Boolean assignment has probability at most
`2^(n+1)*exp(-2*s*delta^2)`. Deduce the sample-size requirement for failure
probability `eta` and that an exact sample optimiser loses at most
`2*delta*m` clauses on the original input.

Build the threshold-counting circuit and its unique-extension CNF encoding,
including the `O_k(s)` gate count using a linear-size Boolean adder network.
Combine with binary search and witness recovery to give a reduction from
sample optimisation to fixed-width SAT. State its runtime in terms of the
supplied SAT solver. An approximation reduction does not establish an
approximation-hardness conjecture or instantiate the announced algorithm.

### M22. Faster algorithms and classical circuit lower bounds

Dependencies: M05, M06, M11, M17.

Reuse CSLib circuit size, counting, synthesis, and Shannon theory. Define
families and `SIZE(O(n))`, `P/poly`, succinctly addressed witnesses, and
`E^NP = DTIME(2^{O(n)})^NP`, with query writing charged to running time.
Build clocked universal machines, oracle computation/verifier bridges,
padding, and the nondeterministic time hierarchy needed for the argument.
Construct locally addressable Cook–Levin tableaux with linear-size circuits
for their addressed constraints; supply the binary arithmetic and indexing
circuits with size bounds.

Prove the universal-witness-circuit consequence of the hypothesis
`E^NP ⊆ SIZE(O(n))`. Then prove Williams's classical implication
`¬ETH → E^NP ⊈ SIZE(O(n))` by guessing a succinct witness and using the
assumed arbitrarily-small-exponent 3-SAT solvers to verify its local
constraints. This requires the nonuniform witness-selection argument and
the time-hierarchy contradiction, not just ordinary circuit counting.
The unconditional stronger lower bound announced with the new algorithm is
outside scope. [Williams, Theorem 6.1](#references)

## Dependency and launch order

The dependency graph is the milestone dependency lists above; in particular,
M08's probability dependency is M19, and M10 uses only its deterministic
branching lemmas. An order satisfying all dependencies is:

1. M01–M07, M15, M19: finite counting, encodings, implementation/bit-cost
   bridges, reductions, classical completeness, baseline algorithms, Boolean
   algebra, and probability foundations.
2. M08–M11, M14, M16–M18: established SAT algorithms, self-reductions,
   sparsification, hypotheses, fine-grained transfer, and effective algebra.
3. M12, M13, M20–M22: parameterised algorithms, applications, pseudorandom
   codes, optimisation, and algorithms-to-lower-bounds.

Start implementation with M01, M02 and the needed pieces of M03, then the
unique-extension theorem in M06 after its prerequisites. These give early,
independently useful contributions. Keep the longer classical results in
their numbered milestones; their prerequisites remain explicit work.

Completion means the mathematical results, executable constructions and
resource theorems above are implemented against existing APIs. Definitions
alone, a successful external proof build, or a list of conditional corollaries
does not discharge a milestone.

## References

These specify classical results and conventions. They do not prescribe a
file-by-file port of an existing formalisation.

- **Complexity foundations:** [Arora–Barak, *Computational Complexity: A Modern Approach*](https://theory.cs.princeton.edu/complexity/),
  especially verifiers, circuits, counting, and pseudorandomness; and
  [Impagliazzo–Paturi–Zane, *Which Problems Have Strongly Exponential Complexity?*](https://www.ccs.neu.edu/home/viola/classes/papers/ImpagliazzoPaturiZane01Which.pdf)
  for subexponential reductions and sparsification.
- **Counting sparsification:** [Dell–Husfeldt–Marx–Taslaman–Wahlén, *Exponential Time Complexity of the Permanent and the Tutte Polynomial*](https://arxiv.org/abs/1206.1775),
  including its counting/disjoint sparsification appendix.
- **Schöning:** [*A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems*](https://www.eecs.harvard.edu/~michaelm/CS223/schoning99.pdf).
- **Jerrum–Valiant–Vazirani:** [*Random Generation of Combinatorial Structures from a Uniform Distribution*](https://ics.uci.edu/~vazirani/JVV.pdf).
- **Naor–Naor:** [*Small-bias Probability Spaces: Efficient Constructions and Applications*](https://www.wisdom.weizmann.ac.il/~naor/PAPERS/bias.pdf).
- **Sipser–Spielman:** [*Expander Codes*](https://cs-www.cs.yale.edu/homes/spielman/PAPERS/expandersIT.pdf).
- **Williams:** [*Improving Exhaustive Search Implies Superpolynomial Lower Bounds*](https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf),
  Theorem 6.1 for M22; [*A New Algorithm for Optimal 2-Constraint Satisfaction and Its Implications*](https://doi.org/10.1016/j.tcs.2005.09.023)
  for the split-and-list background to M14.
