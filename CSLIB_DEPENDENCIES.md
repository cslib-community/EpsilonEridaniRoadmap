# CSLib dependencies

EpsilonEridani depends on [CSLib](https://github.com/leanprover/cslib) `main`, which the
scheduled *Update configured upstreams* workflow advances. Some roadmap items build on CSLib
material that is still in an open pull request. Those pull requests are listed in
[`cslib-dependencies.toml`](cslib-dependencies.toml), which is the authority; this page explains
the rules.

## Rules

1. **Name the pull request.** A roadmap item that needs material from an unmerged CSLib pull
   request cites it as `CSLib #N`, and the registry entry for `#N` lists that item under
   `used_by`.
2. **Pin the reviewed revision.** Each entry records the pull request's head commit that the
   roadmap follows, and the pull requests it is stacked on.
3. **Build a stand-in, shaped like the pull request.** EpsilonEridani carries each module the
   pull request adds or changes, as it stands at the pinned head, at the same path under
   `EpsilonEridani/Pending/`, so
   `Cslib/Crypto/Game.lean` becomes `EpsilonEridani/Pending/Cslib/Crypto/Game.lean`, with every
   declaration in namespace `EpsilonEridani.Pending.Cslib.…` and otherwise the same names and
   statements as at the pinned head. The module docstring cites the pull request and pinned
   commit. Code from the pull request may be copied with attribution under CSLib's Apache 2.0
   licence. Stand-ins are ordinary EpsilonEridani targets: building one discharges the roadmap
   item that requires it.
4. **Never wait.** An open pull request is never a reason to leave a gap or postpone a target.

## Lifecycle

`python3 scripts/check_cslib_dependencies.py` reports one action per entry:

| State | Action |
|---|---|
| Open, head unchanged | None. |
| Open, head moved | Review the new diff, update `head`, and update the stand-in to match. |
| Merged, not yet in EpsilonEridani's CSLib pin | Wait for the next upstream update PR. |
| Merged and in EpsilonEridani's CSLib pin | Swap: delete the stand-in, replace `EpsilonEridani.Pending.Cslib` with `Cslib` in imports and names, and remove the entry. |
| Closed without merging | Move the stand-in out of `Pending/` into EpsilonEridani's own namespace, and remove the entry. |

The swap is a deletion plus a rename, so dependent work does not change.
