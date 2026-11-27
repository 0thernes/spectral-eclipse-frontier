#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Independent exact arbitrary-precision & Sturm-sequence reference oracle.

Provides zero-rounding-error verification of Early State Exclusion (ESE) for
integer and half-integer symmetric persymmetric PST chains via exact rational
Chebyshev polynomials and Sturm root counting on (-1, 1), plus 80-digit mpmath
verification for non-symmetric complex chains (Theorem 9) and Mandelstam-Tamm
quantum speed limits (Theorem 10).
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction

import mpmath as mp
import sympy as sp

mp.mp.dps = 80


@dataclass(frozen=True)
class ExactChainSummary:
    label: str
    n: int
    has_ese: bool
    exact_sturm_roots_in_open_interval: int
    first_ese_tau_mp80: str | None
    b0_sq_exact: str
    qsl_pi_over_2sigma_mp80: str
    eta_mp80: str | None


def exact_persymmetric_weights_q(spectrum: Sequence[Fraction]) -> list[Fraction]:
    """Compute exact normalized persymmetric spectral weights w_k in Q."""
    n = len(spectrum)
    if n < 2:
        raise ValueError("Spectrum must have at least 2 eigenvalues.")
    for i in range(n - 1):
        if not (spectrum[i] < spectrum[i + 1]):
            raise ValueError("Spectrum must be strictly increasing.")
    unnorm: list[Fraction] = []
    for k in range(n):
        prod = Fraction(1)
        for j in range(n):
            if j != k:
                prod *= abs(spectrum[k] - spectrum[j])
        unnorm.append(Fraction(1, 1) / prod)
    total = sum(unnorm, Fraction(0))
    return [u / total for u in unnorm]


def exact_energy_variance_q(spectrum: Sequence[Fraction]) -> Fraction:
    """Exact Theorem 10 energy variance b_0^2 = Var_{e_0}(J) in Q."""
    w = exact_persymmetric_weights_q(spectrum)
    mean = sum((wk * lk for wk, lk in zip(w, spectrum)), Fraction(0))
    return sum((wk * (lk - mean) ** 2 for wk, lk in zip(w, spectrum)), Fraction(0))


def exact_sturm_ese_root_count(spectrum: Sequence[Fraction], scale_factor: int = 1) -> tuple[int, sp.Poly]:
    """Count EXACT real zeros of A(t) on (0, pi) for symmetric integer/half-integer spectra.

    If `spectrum` consists of integers (scale_factor=1), A(t) = P(cos t) where
    P(u) = sum w_k T_{|lam_k|}(u) and t in (0, pi) <-> u = cos(t) in (-1, 1).
    If `spectrum` consists of half-integers (scale_factor=2), A(t) = P(cos(t/2))
    where u = cos(t/2) in (0, 1) for t in (0, pi)!
    Uses exact rational SymPy Sturm real-root isolation (`sp.count_roots`).
    """
    w = exact_persymmetric_weights_q(spectrum)
    u = sp.Symbol("u")
    poly_expr = sp.Integer(0)
    for wk, lk in zip(w, spectrum):
        deg_f = abs(lk) * scale_factor
        if deg_f.denominator != 1:
            raise ValueError(f"Scaled frequency {deg_f} is not an integer")
        deg = int(deg_f.numerator)
        poly_expr += sp.Rational(wk.numerator, wk.denominator) * sp.chebyshevt(deg, u)
    poly = sp.Poly(sp.expand(poly_expr), u, domain="QQ")
    lo = sp.Integer(-1) if scale_factor == 1 else sp.Integer(0)
    hi = sp.Integer(1)
    # Use the square-free part so every distinct real root is counted with multiplicity 1.
    sqf_poly = sp.Poly(sp.sqf_part(poly.as_expr()), u, domain="QQ")
    distinct_closed = int(sp.count_roots(sqf_poly, lo, hi))
    distinct_open = (
        distinct_closed
        - (1 if sqf_poly.eval(lo) == 0 else 0)
        - (1 if sqf_poly.eval(hi) == 0 else 0)
    )
    return distinct_open, poly


def mp80_first_ese_root(spectrum: Sequence[Fraction], scale_factor: int = 1) -> mp.mpf | None:
    """Compute the first interior ESE zero tau in (0, pi) to 80 decimal digits via mpmath."""
    roots, poly = exact_sturm_ese_root_count(spectrum, scale_factor=scale_factor)
    if roots == 0:
        return None
    u = sp.Symbol("u")
    lo = -1 if scale_factor == 1 else 0
    # Isolate real roots in (lo, 1) exactly, take the LARGEST u in (lo, 1) -> SMALLEST t = arccos(u) * scale_factor!
    intervals = sp.Poly(sp.sqf_part(poly.as_expr()), u, domain="QQ").intervals(inf=lo, sup=1)
    interior = []
    for (a, b), _mult in intervals:
        if (a > lo and b < 1) or (b > lo and a < 1 and not (a == b and a in (lo, 1))):
            interior.append((a, b))
    if not interior:
        return None
    # Largest u corresponds to smallest t!
    a_r, b_r = max(interior, key=lambda pair: pair[0])
    w = exact_persymmetric_weights_q(spectrum)
    w_mp = [mp.mpf(wk.numerator) / mp.mpf(wk.denominator) for wk in w]
    l_mp = [mp.mpf(lk.numerator) / mp.mpf(lk.denominator) for lk in spectrum]

    def f_t(t: mp.mpf) -> mp.mpf:
        return sum(wk * mp.cos(lk * t) for wk, lk in zip(w_mp, l_mp))

    t_lo = mp.mpf(scale_factor) * mp.acos(mp.mpf(b_r.p) / mp.mpf(b_r.q))
    t_hi = mp.mpf(scale_factor) * mp.acos(mp.mpf(a_r.p) / mp.mpf(a_r.q))
    # Bisect in 80-digit arithmetic to 1e-70!
    f_lo = f_t(t_lo)
    for _ in range(250):
        mid = (t_lo + t_hi) / 2
        f_mid = f_t(mid)
        if f_mid == 0:
            t_lo = t_hi = mid
            break
        if (f_lo > 0) == (f_mid > 0):
            t_lo, f_lo = mid, f_mid
        else:
            t_hi = mid
    return (t_lo + t_hi) / 2


def verify_canonical_suite() -> list[ExactChainSummary]:
    """Run exact Sturm + 80-digit mpmath oracle on the complete Theorem 1-10 canonical suite."""
    cases: list[tuple[str, list[Fraction], int]] = [
        ("4x4_noESE_1_3", [Fraction(k, 2) for k in (-3, -1, 1, 3)], 2),
        ("4x4_ESE_3_5", [Fraction(k, 2) for k in (-5, -3, 3, 5)], 2),
        ("5x5_noESE_1_2", [Fraction(k) for k in (-2, -1, 0, 1, 2)], 1),
        ("5x5_ESE_3_4", [Fraction(k) for k in (-4, -3, 0, 3, 4)], 1),
        ("6x6_noESE_1_3_5", [Fraction(k, 2) for k in (-5, -3, -1, 1, 3, 5)], 2),
        ("7x7_noESE_1_2_3", [Fraction(k) for k in (-3, -2, -1, 0, 1, 2, 3)], 1),
        ("7x7_ESE_3_4_5", [Fraction(k) for k in (-5, -4, -3, 0, 3, 4, 5)], 1),
        ("8x8_rupture_m1", [Fraction(k, 2) for k in (-11, -9, -7, -1, 1, 7, 9, 11)], 2),
        ("9x9_critical_1_2_3_4", [Fraction(k) for k in (-4, -3, -2, -1, 0, 1, 2, 3, 4)], 1),
        ("9x9_critical_1_20_21_22", [Fraction(k) for k in (-22, -21, -20, -1, 0, 1, 20, 21, 22)], 1),
        ("11x11_subcrit_m5", [Fraction(k) for k in (-13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13)], 1),
        ("11x11_supercrit_m6", [Fraction(k) for k in (-15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15)], 1),
    ]
    out: list[ExactChainSummary] = []
    for label, spec, sf in cases:
        cnt, _ = exact_sturm_ese_root_count(spec, scale_factor=sf)
        b0_sq = exact_energy_variance_q(spec)
        sigma = mp.sqrt(mp.mpf(b0_sq.numerator) / mp.mpf(b0_sq.denominator))
        qsl = mp.pi / (2 * sigma)
        tau = mp80_first_ese_root(spec, scale_factor=sf)
        eta = (qsl / tau) if tau is not None else None
        out.append(
            ExactChainSummary(
                label=label,
                n=len(spec),
                has_ese=(cnt > 0),
                exact_sturm_roots_in_open_interval=cnt,
                first_ese_tau_mp80=mp.nstr(tau, 25) if tau is not None else None,
                b0_sq_exact=f"{b0_sq.numerator}/{b0_sq.denominator}",
                qsl_pi_over_2sigma_mp80=mp.nstr(qsl, 25),
                eta_mp80=mp.nstr(eta, 25) if eta is not None else None,
            )
        )
    # Add Theorem 9 J_{1,4} exact complex check at 80 digits!
    j14_spec = [Fraction(k) for k in (0, 1, 4, 9, 10)]
    w_j14 = exact_persymmetric_weights_q(j14_spec)
    b0_j14 = exact_energy_variance_q(j14_spec)
    assert b0_j14 == Fraction(15, 1), f"J14 b0^2 expected 15, got {b0_j14}"
    tau_j14 = mp.pi / 3
    amp_j14 = sum(
        (mp.mpf(wk.numerator) / mp.mpf(wk.denominator)) * mp.exp(-1j * mp.mpf(lk.numerator) * tau_j14)
        for wk, lk in zip(w_j14, j14_spec)
    )
    assert abs(amp_j14) < mp.mpf("1e-75"), f"J14 complex ESE residual too large: {abs(amp_j14)}"
    qsl_j14 = mp.pi / (2 * mp.sqrt(15))
    out.append(
        ExactChainSummary(
            label="5x5_J14_complex_ESE",
            n=5,
            has_ese=True,
            exact_sturm_roots_in_open_interval=1,
            first_ese_tau_mp80=mp.nstr(tau_j14, 25),
            b0_sq_exact="15/1",
            qsl_pi_over_2sigma_mp80=mp.nstr(qsl_j14, 25),
            eta_mp80=mp.nstr(qsl_j14 / tau_j14, 25),
        )
    )
    return out


if __name__ == "__main__":
    results = verify_canonical_suite()
    print(json.dumps([r.__dict__ for r in results], indent=2))
