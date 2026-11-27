#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Pre-registered statistical analysis of the QRNG diagonal-disorder study.

Implements the exact analysis plan locked in PREREGISTRATION.md BEFORE execution:
  - Paired 10,000-sign-flip two-sided permutation tests on d_s = m_ctrl(s) - m_treat(s)
    at the primary endpoint eps = 0.05 (K = 30 paired QRNG seeds per hypothesis).
  - Holm-Bonferroni FWER correction across the 4 primary hypotheses (H1, H2, H3, H4).
  - Median difference, mean difference, paired Cohen's d_z, Cliff's delta, and
    10,000-resample percentile bootstrap 95% confidence intervals.
  - Full reporting across all 5 disorder levels eps in {0.00, 0.01, 0.02, 0.05, 0.10}
    plus exploratory power-law scaling m(eps) ~ eps^beta.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from numpy.typing import NDArray

ROOT = Path(__file__).resolve().parents[1]
IN_JSON = ROOT / "results" / "qgtl_qrng_study.json"
OUT_JSON = ROOT / "results" / "qgtl_qrng_analysis.json"


def cliffs_delta(x: NDArray[np.float64], y: NDArray[np.float64]) -> float:
    """Cliff's delta P(x > y) - P(x < y) (positive when ctrl > treat)."""
    gt = 0
    lt = 0
    for xi in x:
        gt += int(np.sum(xi > y))
        lt += int(np.sum(xi < y))
    return float((gt - lt) / (len(x) * len(y)))


def paired_permutation_p(diffs: NDArray[np.float64], n_perm: int = 10000, seed: int = 20260020) -> float:
    """Two-sided paired sign-flip permutation p-value (exact denominator n_perm + 1)."""
    rng = np.random.default_rng(seed)
    obs = abs(float(np.mean(diffs)))
    signs = rng.choice([-1.0, 1.0], size=(n_perm, len(diffs)))
    perm_means = np.abs(np.mean(signs * diffs[None, :], axis=1))
    exceed = int(np.sum(perm_means >= obs - 1e-15))
    return float((exceed + 1) / (n_perm + 1))


def bootstrap_ci_mean_diff(
    diffs: NDArray[np.float64], n_boot: int = 10000, seed: int = 20260021
) -> tuple[float, float]:
    """10,000-resample percentile bootstrap 95% CI for mean(ctrl - treat)."""
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, len(diffs), size=(n_boot, len(diffs)))
    boot_means = np.mean(diffs[idx], axis=1)
    lo, hi = np.percentile(boot_means, [2.5, 97.5])
    return float(lo), float(hi)


def holm_bonferroni(pvals: list[float]) -> list[float]:
    """Step-down Holm-Bonferroni FWER adjusted p-values."""
    m = len(pvals)
    order = sorted(range(m), key=lambda i: pvals[i])
    adj = [0.0] * m
    running_max = 0.0
    for rank, idx in enumerate(order):
        val = min(1.0, (m - rank) * pvals[idx])
        running_max = max(running_max, val)
        adj[idx] = running_max
    return adj


def main() -> int:
    raw = json.loads(IN_JSON.read_text(encoding="utf-8"))
    arms_out = []
    primary_pvals = []

    for arm_idx, arm in enumerate(raw["arms"]):
        levels_summary = []
        primary_record = None
        eps_nz = []
        treat_nz = []
        for lv in arm["levels"]:
            eps = float(lv["eps"])
            t_arr = np.array(lv["treat_min"], dtype=np.float64)
            c_arr = np.array(lv["ctrl_min"], dtype=np.float64)
            diffs = c_arr - t_arr
            mean_d = float(np.mean(diffs))
            sd_d = float(np.std(diffs, ddof=1))
            dz = float(mean_d / sd_d) if sd_d > 1e-15 else 0.0
            cd = cliffs_delta(c_arr, t_arr)
            p_perm = paired_permutation_p(diffs, n_perm=10000, seed=20260020 + arm_idx * 10 + int(eps * 100))
            ci_lo, ci_hi = bootstrap_ci_mean_diff(diffs, n_boot=10000, seed=20260120 + arm_idx * 10 + int(eps * 100))
            rec = {
                "eps": eps,
                "treat_median": float(np.median(t_arr)),
                "treat_mean": float(np.mean(t_arr)),
                "treat_iqr": float(np.percentile(t_arr, 75) - np.percentile(t_arr, 25)),
                "ctrl_median": float(np.median(c_arr)),
                "ctrl_mean": float(np.mean(c_arr)),
                "ctrl_iqr": float(np.percentile(c_arr, 75) - np.percentile(c_arr, 25)),
                "diff_median": float(np.median(diffs)),
                "diff_mean": mean_d,
                "diff_ci95_lo": ci_lo,
                "diff_ci95_hi": ci_hi,
                "cohens_dz": dz,
                "cliffs_delta": cd,
                "p_perm_two_sided": p_perm,
            }
            levels_summary.append(rec)
            if abs(eps - 0.05) < 1e-9:
                primary_record = rec
            if eps > 0.0:
                eps_nz.append(eps)
                treat_nz.append(max(float(np.median(t_arr)), 1e-12))
        assert primary_record is not None
        primary_pvals.append(primary_record["p_perm_two_sided"])
        # Exploratory power-law fit log(m_med) = beta * log(eps) + c
        slope, intercept = np.polyfit(np.log(eps_nz), np.log(treat_nz), 1)
        arms_out.append(
            {
                "id": arm["id"],
                "treat_name": arm["treat_name"],
                "ctrl_name": arm["ctrl_name"],
                "primary_eps05": primary_record,
                "exploratory_power_law_beta": float(slope),
                "exploratory_power_law_prefactor": float(math.exp(intercept)),
                "all_levels": levels_summary,
            }
        )

    p_adj = holm_bonferroni(primary_pvals)
    for arm_rec, pa in zip(arms_out, p_adj):
        arm_rec["primary_eps05"]["p_holm_bonferroni"] = pa
        arm_rec["primary_eps05"]["significant_fwer_005"] = bool(
            pa < 0.05 and arm_rec["primary_eps05"]["diff_median"] > 0.0
        )

    out_payload = {
        "preregistration": raw["preregistration"],
        "qrng_version": raw["qrng_version"],
        "n_seeds": raw["n_seeds"],
        "qgtl_theorem10": raw["qgtl_theorem10"],
        "primary_family_fwer_alpha": 0.05,
        "arms": arms_out,
    }
    OUT_JSON.write_text(json.dumps(out_payload, indent=2) + "\n", encoding="utf-8")

    print("=== Pre-Registered Primary Endpoint Summary (eps = 0.05, K = 30 paired QRNG seeds) ===")
    for arm_rec in arms_out:
        p = arm_rec["primary_eps05"]
        print(
            f"  {arm_rec['id']}: treat_med={p['treat_median']:.5f}, ctrl_med={p['ctrl_median']:.5f}, "
            f"mean_diff={p['diff_mean']:+.5f} [{p['diff_ci95_lo']:+.5f}, {p['diff_ci95_hi']:+.5f}], "
            f"dz={p['cohens_dz']:+.2f}, Cliff={p['cliffs_delta']:+.3f}, "
            f"p_perm={p['p_perm_two_sided']:.4g}, p_Holm={p['p_holm_bonferroni']:.4g}, "
            f"sig={p['significant_fwer_005']}, beta={arm_rec['exploratory_power_law_beta']:.2f}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
