# EpsilonEridaniRoadmap

Human-owned roadmaps for [EpsilonEridani](https://github.com/cslib-community/EpsilonEridani), a
Lean library downstream of [CSLib](https://github.com/leanprover/cslib). Each roadmap specifies
material we want built in EpsilonEridani, in layers that rest on CSLib, Mathlib, or earlier
layers.

## Roadmaps

| Roadmap | Scope |
|---|---|
| [PrivateKeyEncryption](EpsilonEridaniRoadmap/PrivateKeyEncryption/README.md) | Katz–Lindell Chapters 2–5: perfect secrecy, EAV and CPA security from PRGs and PRFs, MACs, CCA security and authenticated encryption |
| [OneWayFunctions](EpsilonEridaniRoadmap/OneWayFunctions/README.md) | Katz–Lindell Chapter 8: PPT computation, one-way functions, Goldreich–Levin, and PRGs, PRFs and PRPs from one-way permutations |

Each roadmap's `README.md` is its specification. Its `Suggested.lean` states, with `sorry`, the
targets that can already be written in Lean; statements are added as their definitions land.
Completed roadmaps move to [`Completed/`](Completed/).

## CSLib dependencies

Roadmap items that build on open CSLib pull requests name them, and
[`cslib-dependencies.toml`](cslib-dependencies.toml) records each pull request's pinned revision
and users. [CSLIB_DEPENDENCIES.md](CSLIB_DEPENDENCIES.md) gives the rules, and
`python3 scripts/check_cslib_dependencies.py` reports what each entry needs.

## Pull requests in EpsilonEridani

A pull request names the roadmap it advances with a line `Roadmap: <Roadmap>`, or
`Roadmap: none`, and cites the item it discharges, for example `PrivateKeyEncryption, Theorem
2.12`.

## Building

```sh
lake exe cache get
lake build
```
