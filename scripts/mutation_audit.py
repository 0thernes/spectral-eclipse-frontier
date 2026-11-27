#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Build Standard B13 surgical mutation testing audit.

Injects 10 targeted semantic mutants into temporary copies of
`python/spectral_eclipse/core.py` and `reference/exact_oracle.py`, running
`pytest` on each mutant in an isolated copy of the source tree (never
modifying the working tree) and asserting a 100% kill rate.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Mutant:
    mutant_id: str
    rel_path: str
    target: str
    replacement: str
    description: str


MUTANTS: list[Mutant] = [
    Mutant(
        "M01_qsl_factor",
        "python/spectral_eclipse/core.py",
        "return math.pi / (2.0 * self.off_b[0])",
        "return math.pi / (4.0 * self.off_b[0])",
        "Halve QSL bound factor pi/(2 b0) -> pi/(4 b0)",
    ),
    Mutant(
        "M02_weight_sign",
        "python/spectral_eclipse/core.py",
        "log_inv[k] = -float(np.sum(np.log(diffs)))",
        "log_inv[k] = float(np.sum(np.log(diffs)))",
        "Flip sign of log Hochstadt weights",
    ),
    Mutant(
        "M03_mono_check",
        "python/spectral_eclipse/core.py",
        "if not bool(np.all(np.diff(lam) > 0.0)):",
        "if False:",
        "Disable strict-monotonicity input validation",
    ),
    Mutant(
        "M04_mgs_pass",
        "python/spectral_eclipse/core.py",
        "b_out[j] = beta",
        "b_out[j] = beta * 1.01",
        "Perturb Lanczos off-diagonal hopping by +1%",
    ),
    Mutant(
        "M05_return_phase",
        "python/spectral_eclipse/core.py",
        "phases = -lam * float(t)",
        "phases = lam * float(t)",
        "Reverse time evolution sign in return_amplitude",
    ),
    Mutant(
        "M06_target_parity",
        "python/spectral_eclipse/core.py",
        "signs = np.array([1.0 if ((n - 1 - k) % 2 == 0) else -1.0 for k in range(n)], dtype=np.float64)",
        "signs = np.ones(n, dtype=np.float64)",
        "Drop alternating mirror-parity signs in target_amplitude",
    ),
    Mutant(
        "M07_ese_guard",
        "python/spectral_eclipse/core.py",
        "if prev > FLOAT64_CANCELLATION_MARGIN and re < -FLOAT64_CANCELLATION_MARGIN:",
        "if prev > FLOAT64_CANCELLATION_MARGIN and re < -1.5:",
        "Break ESE zero-crossing detector threshold",
    ),
    Mutant(
        "M08_sturm_interval",
        "reference/exact_oracle.py",
        "lo = sp.Integer(-1) if scale_factor == 1 else sp.Integer(0)",
        "lo = sp.Integer(0)",
        "Restrict odd-chain Sturm root interval to (0, 1) instead of (-1, 1)",
    ),
    Mutant(
        "M09_variance_formula",
        "reference/exact_oracle.py",
        "return sum((wk * (lk - mean) ** 2 for wk, lk in zip(w, spectrum)), Fraction(0))",
        "return sum((wk * lk ** 2 for wk, lk in zip(w, spectrum)), Fraction(0))",
        "Drop mean-centering in exact_energy_variance_q (breaks non-symmetric J14)",
    ),
    Mutant(
        "M10_j14_assert",
        "reference/exact_oracle.py",
        "assert b0_j14 == Fraction(15, 1)",
        "assert b0_j14 == Fraction(16, 1)",
        "Mutate exact rational b0^2 assertion for J_{1,4}",
    ),
]


def main() -> int:
    results = []
    killed = 0
    with tempfile.TemporaryDirectory(prefix="se_mut_") as tmp:
        stage = Path(tmp) / "repo"
        for sub in ("python", "reference", "tests", "results"):
            shutil.copytree(ROOT / sub, stage / sub)
        shutil.copy2(ROOT / "pyproject.toml", stage / "pyproject.toml")

        env = os.environ.copy()
        env["PYTHONPATH"] = str(stage / "python") + os.pathsep + str(stage)

        # Baseline must pass cleanly first
        base = subprocess.run(
            [sys.executable, "-m", "pytest", "-q", str(stage / "tests" / "test_all.py")],
            cwd=stage,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )
        if base.returncode != 0:
            print("ERROR: baseline pytest failed in mutation sandbox:\n" + base.stdout + base.stderr, file=sys.stderr)
            return 1

        for m in MUTANTS:
            fpath = stage / m.rel_path
            orig = fpath.read_text(encoding="utf-8")
            if m.target not in orig:
                print(f"ERROR: mutant {m.mutant_id} target not found in {m.rel_path}", file=sys.stderr)
                return 1
            mutated = orig.replace(m.target, m.replacement, 1)
            fpath.write_text(mutated, encoding="utf-8")
            try:
                proc = subprocess.run(
                    [sys.executable, "-m", "pytest", "-q", "-x", str(stage / "tests" / "test_all.py")],
                    cwd=stage,
                    env=env,
                    check=False,
                    capture_output=True,
                    text=True,
                )
                is_killed = proc.returncode != 0
                if is_killed:
                    killed += 1
                results.append(
                    {
                        "id": m.mutant_id,
                        "file": m.rel_path,
                        "description": m.description,
                        "status": "KILLED" if is_killed else "SURVIVED",
                    }
                )
            finally:
                fpath.write_text(orig, encoding="utf-8")

    report = {
        "total_mutants": len(MUTANTS),
        "killed": killed,
        "survived": len(MUTANTS) - killed,
        "kill_rate": killed / len(MUTANTS),
        "mutants": results,
    }
    out_path = ROOT / "results" / "mutation_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if killed == len(MUTANTS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
