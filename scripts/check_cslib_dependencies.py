#!/usr/bin/env python3
"""Report the action each entry of cslib-dependencies.toml needs.

Reads the registry, asks GitHub (through the authenticated `gh` CLI) for each pull request's
state, and compares merged pull requests with the CSLib revision pinned in EpsilonEridani's
lake-manifest.json. See CSLIB_DEPENDENCIES.md for the lifecycle.

Usage: python3 scripts/check_cslib_dependencies.py [--content-ref main]
Exit status is 1 when any entry needs an action, 0 otherwise.
"""
from __future__ import annotations

import argparse
import base64
import json
import pathlib
import subprocess
import sys
import tomllib

CSLIB = "leanprover/cslib"
CONTENT = "cslib-community/EpsilonEridani"
REGISTRY = pathlib.Path(__file__).resolve().parent.parent / "cslib-dependencies.toml"


def gh(path: str) -> dict | None:
    result = subprocess.run(["gh", "api", path], capture_output=True, text=True)
    if result.returncode != 0:
        return None
    return json.loads(result.stdout)


def content_file(path: str, ref: str) -> str | None:
    data = gh(f"repos/{CONTENT}/contents/{path}?ref={ref}")
    if data is None:
        return None
    return base64.b64decode(data["content"]).decode()


def cslib_pin(ref: str) -> str:
    manifest = json.loads(content_file("lake-manifest.json", ref) or "{}")
    for package in manifest.get("packages", []):
        if package.get("name") == "cslib":
            return package["rev"]
    sys.exit(f"no cslib package in {CONTENT}@{ref} lake-manifest.json")


def contains(base: str, commit: str) -> bool:
    """True when `commit` is an ancestor of (or equal to) `base` in CSLib."""
    comparison = gh(f"repos/{CSLIB}/compare/{commit}...{base}")
    return comparison is not None and comparison["status"] in ("ahead", "identical")


def stand_in(module: str) -> str:
    return "EpsilonEridani/Pending/" + module


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--content-ref", default="main")
    args = parser.parse_args()

    entries = tomllib.loads(REGISTRY.read_text())["pr"]
    numbers = {entry["number"] for entry in entries}
    pin = cslib_pin(args.content_ref)
    print(f"EpsilonEridani@{args.content_ref} pins CSLib {pin[:12]}\n")

    pending = 0
    for entry in entries:
        number = entry["number"]
        pr = gh(f"repos/{CSLIB}/pulls/{number}")
        if pr is None:
            print(f"#{number}: cannot read the pull request")
            pending += 1
            continue
        missing = [n for n in entry.get("depends_on", []) if n not in numbers]
        present = [m for m in entry["modules"]
                   if content_file(stand_in(m), args.content_ref) is not None]

        if pr["merged_at"]:
            if contains(pin, pr["merge_commit_sha"]):
                action = "swap: delete the stand-in, use CSLib's module, remove the entry"
            else:
                action = "wait for the next CSLib upstream update"
        elif pr["state"] == "closed":
            action = "closed unmerged: move the stand-in out of Pending/, remove the entry"
        elif pr["head"]["sha"] != entry["head"]:
            action = (f"head moved {entry['head'][:12]} -> {pr['head']['sha'][:12]}: "
                      "review, re-pin, update the stand-in")
        else:
            action = None

        status = "merged" if pr["merged_at"] else pr["state"]
        print(f"#{number} [{status}] {entry['title']}")
        print(f"  stand-ins in EpsilonEridani: {len(present)}/{len(entry['modules'])}")
        if missing:
            print(f"  depends on unregistered PRs: {missing}")
        print(f"  action: {action or 'none'}")
        pending += action is not None or bool(missing)
    return 1 if pending else 0


if __name__ == "__main__":
    sys.exit(main())
