# Epsilon Eridani Roadmap

This repository holds the human-directed plans for
[Epsilon Eridani](https://github.com/cslib-community/EpsilonEridani), an AI-built Lean
library for computer science downstream of [CSLib](https://github.com/leanprover/cslib).
It is where we decide what the library should contain and what its definitions and
results should mean. The implementations live in the core repository; the shared
[Tau Ceti review engine](https://github.com/TauCetiProject/TauCetiReview) helps assess them.

A good roadmap gives contributors something worth building and reviewers a clear
way to judge the result. Subject expertise matters here: choosing useful interfaces,
getting hypotheses right, and explaining how a theory fits together are central to
the project. AI assistance can help with research, drafts, and Lean prototypes; humans
review and approve the specifications.

## Roadmaps

There are no approved roadmap areas yet. Proposals for the first areas are welcome!
Open a pull request with a concrete specification and enough context for someone
else to understand why the development will be useful.

Active areas belong under `EpsilonEridaniRoadmap/`, with one directory per area.
Each area has a `README.md` describing its scope and milestones, and may include a
`Suggested.lean` file with proposed interfaces. The area's README is the specification;
Lean prototypes help make it precise. Maintainers can move completed areas to
`Completed/` after checking the implementation against that specification.

## Writing a roadmap

Start from the computer science you want to make available. Explain the objects,
the results about them, and the uses that motivate the development. A contributor
should be able to take a milestone and implement it without having to invent its
meaning or guess which notion you intended.

- **Make the definitions usable.** Include the basic lemmas, constructions, and
  connections that later users will need. Reaching a named theorem is valuable, but
  so is leaving a library that supports the next theorem.
- **Account for prerequisites.** Ground each milestone in existing CSLib, Mathlib,
  or Epsilon Eridani material, or in an explicitly identified roadmap target. If a
  required piece is missing, include building it in the plan.
- **Choose the interface.** Specify assumptions, conventions, representations, and
  the intended level of generality. Include examples that distinguish the intended
  definition from a plausible but unhelpful alternative.
- **Give the area clear boundaries.** Say which results belong here and identify
  dependencies on other areas. Put harder targets in later milestones with a clear
  dependency order; every listed target should be work we intend to complete.
- **Cite the sources.** Point readers to the relevant papers, textbooks, and existing
  formalizations. Give enough detail to locate the particular definitions and results
  being requested, and preserve attribution when adapting existing work.

These principles follow the
[Tau Ceti roadmap guidance](https://github.com/TauCetiProject/TauCetiRoadmap#writing-a-roadmap),
adapted to Epsilon Eridani's dependencies and subject matter.

### Working with CSLib and Mathlib

Look for existing APIs before proposing new ones, including work under review
upstream. Prefer the language and design choices of CSLib and Mathlib when they
already express the concept. Cite the declarations or PRs that informed a proposed
interface so both implementors and reviewers can find them.

If a roadmap needs material absent from the current dependencies, make developing
that material an explicit target. Explain how it should connect to the upstream
interfaces as they evolve. A roadmap should give contributors a coherent development
to build against the project's actual dependency pins.

### Lean prototypes

Use `Suggested.lean` to check that proposed structures and theorem statements fit
together. This package depends on Epsilon Eridani, so prototypes can import existing
`EpsilonEridani.*`, CSLib, and Mathlib modules. Epsilon Eridani's root module is empty;
import the individual modules you need.

Proofs in a roadmap prototype may use `sorry`. Make the definitions and hypotheses
as explicit as possible so a reviewer can check what is being asked. In particular,
an arbitrary `Prop` field does not specify a missing mathematical condition: state
the condition, or explain in the prose which prerequisite is needed to state it.
Introduce each prototype as a suggested interface; the README remains the complete
account of the area's goals.

## How changes are made

Anyone can propose a roadmap or improve an existing one through a pull request.
Explain the scope, the supporting references, and the design choices that need
attention. Maintainers review changes to the specifications; a passing build alone
does not establish that the proposed statements express the intended theory.

Implementation belongs in the
[core repository](https://github.com/cslib-community/EpsilonEridani). Keep roadmap
changes focused on what should be built, and use issues to discuss omissions,
ambiguous statements, or competing interfaces before a large implementation grows
around them.

Before starting substantial work, check open issues and PRs and describe the targets
you intend to take in a roadmap issue. Link the implementation PRs back to that
discussion so others can see what is in progress. Automated intentions management,
shared claims, and generated progress reports have not been enabled for this project.

## Building

With [Lean installed through elan](https://lean-lang.org/install/), run from this
checkout:

```bash
lake exe cache get
lake build
```

The committed toolchain and Lake manifest select the dependencies. CI builds the
active roadmap and completed-area Lean libraries; prototype proofs may contain
`sorry`. Finished implementations in the core repository must satisfy its stricter
build and review checks.
