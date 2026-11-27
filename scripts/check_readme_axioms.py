#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Verify that a Lean axiom audit log (default: results/lean-axioms-all.log) contains
strictly standard axioms, passes the exhaustive Lean.collectAxioms sentinel, and matches
README.md's verbatim #print axioms block and theorem count.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_LINE_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]$")
NO_AXIOM_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")
EXHAUSTIVE_RE = re.compile(
    r"ALL_THEOREMS_AXIOM_AUDIT_PASS:\s*checked\s+(\d+)\s+theorems.*0 disallowed axioms"
)


def parse_log(text: str) -> dict[str, set[str]]:
    unwrapped = re.sub(r",\n\s+", ", ", text.replace("\r\n", "\n"))
    found: dict[str, set[str]] = {}
    for raw in unwrapped.splitlines():
        line = raw.strip()
        m = AXIOM_LINE_RE.match(line)
        if m:
            axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
            found[m.group(1)] = axioms
            continue
        m2 = NO_AXIOM_RE.match(line)
        if m2:
            found[m2.group(1)] = set()
    return found


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify Lean axiom audit log against standard allowlist and README.md."
    )
    parser.add_argument(
        "--log",
        type=Path,
        default=ROOT / "results" / "lean-axioms-all.log",
        help="Path to the Lean axiom audit log to validate.",
    )
    parser.add_argument(
        "--require-exhaustive",
        action="store_true",
        help="Require the ALL_THEOREMS_AXIOM_AUDIT_PASS exhaustive metaprogram sentinel.",
    )
    args = parser.parse_args()

    log_path: Path = args.log
    readme_path = ROOT / "README.md"
    if not log_path.is_file():
        print(f"ERROR: missing {log_path}", file=sys.stderr)
        return 1
    if not readme_path.is_file():
        print(f"ERROR: missing {readme_path}", file=sys.stderr)
        return 1

    log_text = log_path.read_text(encoding="utf-8")
    log_decls = parse_log(log_text)
    if not log_decls:
        print(f"ERROR: no #print axioms lines parsed from {log_path}", file=sys.stderr)
        return 1

    ex_match = EXHAUSTIVE_RE.search(log_text)
    if args.require_exhaustive and not ex_match:
        print(
            f"ERROR: missing ALL_THEOREMS_AXIOM_AUDIT_PASS sentinel in {log_path}",
            file=sys.stderr,
        )
        return 1

    bad_axioms = {
        name: sorted(ax - ALLOWED) for name, ax in log_decls.items() if not (ax <= ALLOWED)
    }
    if bad_axioms:
        print(f"ERROR: non-standard axioms detected: {bad_axioms}", file=sys.stderr)
        return 1

    readme_text = readme_path.read_text(encoding="utf-8")
    readme_decls = parse_log(readme_text)
    if not readme_decls:
        print("ERROR: README.md has no verbatim #print axioms lines", file=sys.stderr)
        return 1

    mismatches = []
    for name, ax in readme_decls.items():
        if name not in log_decls:
            mismatches.append(f"README cites '{name}' which is absent from {log_path}")
        elif log_decls[name] != ax:
            mismatches.append(
                f"Axiom mismatch for '{name}': README={sorted(ax)} vs log={sorted(log_decls[name])}"
            )

    if ex_match:
        readme_ex = EXHAUSTIVE_RE.search(readme_text)
        if not readme_ex:
            mismatches.append("README.md is missing the verbatim ALL_THEOREMS_AXIOM_AUDIT_PASS sentinel")
        elif readme_ex.group(1) != ex_match.group(1):
            mismatches.append(
                f"Exhaustive theorem count mismatch: README={readme_ex.group(1)} vs log={ex_match.group(1)}"
            )

    if mismatches:
        for msg in mismatches:
            print("ERROR:", msg, file=sys.stderr)
        return 1

    ex_note = f"; exhaustive audit {ex_match.group(1)} theorems (0 disallowed)" if ex_match else ""
    print(
        f"PASS: {len(log_decls)} explicit Lean declarations in {log_path.name} strictly within "
        f"{sorted(ALLOWED)}{ex_note}; {len(readme_decls)} headline declarations verified verbatim in README.md."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
