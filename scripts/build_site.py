#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Assemble the static GitHub Pages portal in build/site/ (WCAG 2.2 AA, strict CSP)."""
from __future__ import annotations

import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"


def main() -> int:
    if SITE.exists():
        shutil.rmtree(SITE)
    SITE.mkdir(parents=True, exist_ok=True)
    shutil.copytree(ROOT / "web", SITE, dirs_exist_ok=True)
    # Copy frozen PDF & results snapshots for download links if present
    assets = SITE / "artifacts"
    assets.mkdir(exist_ok=True)
    for rel in (
        "dist/Donahue_2026_spectral_eclipse_frontier.pdf",
        "results/lean-axioms-all.log",
        "results/polyglot_parity.json",
        "results/qgtl_qrng_analysis.json",
        "results/citation-audit.json",
        "docs/media/social-preview.png",
    ):
        src = ROOT / rel
        if src.is_file():
            shutil.copy2(src, assets / src.name)
    # Prevent Jekyll processing on GitHub Pages
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    print(f"PASS: Assembled static GitHub Pages site at {SITE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
