#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Runnable quickstart showcasing Theorems 4, 5, 6, 7, 9, and 10."""
from __future__ import annotations

import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

from spectral_eclipse import (
    detect_real_ese,
    reconstruct_persymmetric_jacobi,
    return_amplitude,
    target_amplitude,
)


def main() -> int:
    print("=== Spectral Eclipse Frontier Quickstart ===")
    examples = [
        ("Thm 4 (7x7 No-ESE {0,+-1,+-2,+-3})", [-3, -2, -1, 0, 1, 2, 3]),
        ("Thm 4 (7x7 ESE    {0,+-3,+-4,+-5})", [-5, -4, -3, 0, 3, 4, 5]),
        ("Thm 5 (8x8 Rupture m=1)", [-5.5, -4.5, -3.5, -0.5, 0.5, 3.5, 4.5, 5.5]),
        ("Thm 6 (9x9 Critical {0,+-1,+-20..22})", [-22, -21, -20, -1, 0, 1, 20, 21, 22]),
        ("Thm 7 (11x11 Subcritical m=5)", [-13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13]),
        ("Thm 7 (11x11 Supercritical m=6, M*=12)", [-15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15]),
    ]
    for label, spec in examples:
        ch = reconstruct_persymmetric_jacobi([float(x) for x in spec])
        has_ese, tau = detect_real_ese(ch)
        tau_str = f"{tau:.6f}" if tau is not None else "None"
        print(f"{label:40s} | ESE={str(has_ese):5s} | tau={tau_str:10s} | b0^2={ch.b0_sq:8.4f} | QSL={ch.qsl_bound:.6f}")

    # Theorem 9 & 10B: Non-symmetric staggered-field J_{1,4}
    j14 = reconstruct_persymmetric_jacobi([0.0, 1.0, 4.0, 9.0, 10.0])
    a_ese = return_amplitude(j14, math.pi / 3.0)
    t_pst = target_amplitude(j14, math.pi)
    t_ete = target_amplitude(j14, 2.0 * math.pi / 3.0)
    print(f"\nThm 9/10B J_{{1,4}} diag={tuple(round(x, 6) for x in j14.diag_a)}, b0^2={j14.b0_sq:.6f}")
    print(f"  |A(pi/3)|  = {abs(a_ese):.3e}  (exact complex ESE)")
    print(f"  |T(2pi/3)| = {abs(t_ete):.3e}  (exact dual ETE via Thm 10B)")
    print(f"  |T(pi)|    = {abs(t_pst):.12f} (exact PST)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
