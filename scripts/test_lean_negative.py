#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Live negative Lean 4 elaboration tests: confirms the Lean kernel rejects false variants."""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"

NEGATIVE_CASES: list[tuple[str, str]] = [
    (
        "mutated_11x11_threshold_m5",
        """import SpectralEclipse.RuptureAndPhase
theorem bad_m5 : SpectralEclipse.HasESEReal (SpectralEclipse.amp11 1 10 11 12 13) := by
  have h := (SpectralEclipse.odd_rupture_11x11_threshold (m := 5) (by decide)).mpr (by decide)
  norm_num at h
  exact h
""",
    ),
    (
        "mutated_4x4_false_p3",
        """import SpectralEclipse.Chains456
theorem bad_4x4 : ¬SpectralEclipse.HasESEReal (SpectralEclipse.amp4 3 5) := by
  have h := (SpectralEclipse.dichotomy_4x4 (p := 3) (q := 5) ⟨1, rfl⟩ ⟨2, rfl⟩ (by decide) (by decide)).mpr rfl
  exact h
""",
    ),
    (
        "mutated_J14_wrong_variance",
        """import SpectralEclipse.NonVacuity
theorem bad_var : (SpectralEclipse.stagHop 1 4 0) ^ 2 = 16 := by
  have h := SpectralEclipse.NonVacuity.witness_J14_staggered_complex_ESE.2.2.1
  linarith
""",
    ),
]


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="se_lean_neg_") as tmp:
        for name, src in NEGATIVE_CASES:
            f = Path(tmp) / f"{name}.lean"
            f.write_text(src, encoding="utf-8")
            proc = subprocess.run(
                ["lake", "env", "lean", str(f)],
                cwd=LEAN_DIR,
                check=False,
                capture_output=True,
                text=True,
            )
            if proc.returncode == 0:
                print(f"ERROR: negative Lean case '{name}' unexpectedly succeeded!", file=sys.stderr)
                return 1
            print(f"PASS: Lean rejected false variant '{name}' (exit {proc.returncode}).")
    print(f"ALL {len(NEGATIVE_CASES)} NEGATIVE LEAN ELABORATION TESTS PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
