#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Deterministically generate llms-full.txt from canonical repository sources (Build Standard A32)."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SECTIONS: list[tuple[str, str]] = [
    ("Repository Overview (README.md)", "README.md"),
    ("Claims Registry & Falsification Protocol (CLAIMS.md)", "CLAIMS.md"),
    ("Limitations & Epistemic Boundaries (LIMITATIONS.md)", "LIMITATIONS.md"),
    ("Pre-Registration Protocol (PREREGISTRATION.md)", "PREREGISTRATION.md"),
    ("Pre-Registration Deviations Log (DEVIATIONS.md)", "DEVIATIONS.md"),
    ("Statement-Fidelity Audit (docs/statement-fidelity.md)", "docs/statement-fidelity.md"),
    ("Mega-Atlas Boundary Cross-Check (docs/MEGA_ATLAS_CROSSCHECK.md)", "docs/MEGA_ATLAS_CROSSCHECK.md"),
    ("Adversarial Hardening Log (HARDENING_LOG.md)", "HARDENING_LOG.md"),
    ("Replication Protocol (REPLICATION.md)", "REPLICATION.md"),
    ("Formalization Metadata (formalization.yaml)", "formalization.yaml"),
]


def main() -> int:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    header = (
        f"# Spectral Eclipse Frontier (v{version}) — Full LLM Context Bundle\n\n"
        "> Generated deterministically by `scripts/generate_llms_full.py` (Build Standard A32).\n"
        "> Do not hand-edit this file; re-run `python scripts/generate_llms_full.py` after updating sources.\n"
    )
    parts: list[str] = [header]
    missing: list[str] = []
    for title, rel in SECTIONS:
        src = ROOT / rel
        if not src.is_file():
            missing.append(rel)
            continue
        body = src.read_text(encoding="utf-8").replace("\r\n", "\n").strip()
        parts.append(f"\n---\n\n## {title}\n\n{body}\n")
    if missing:
        print(f"ERROR: missing source files for llms-full.txt: {missing}", file=sys.stderr)
        return 1
    out = ROOT / "llms-full.txt"
    out.write_bytes("".join(parts).encode("utf-8"))
    print(f"PASS: Generated {out.name} ({out.stat().st_size} bytes, {len(SECTIONS)} sections, v{version}).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
