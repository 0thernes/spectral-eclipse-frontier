#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Generate all 5 publication-grade vector PDF figures and the 1280x640 social preview PNG.

Uses the Okabe-Ito colorblind-safe palette, clean serif typography matching AMS-LaTeX,
zero overlapping labels, and exact data from the verified engines & QRNG study.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

from spectral_eclipse import reconstruct_persymmetric_jacobi, return_amplitude, target_amplitude

FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)
MEDIA_DIR = ROOT / "docs" / "media"
MEDIA_DIR.mkdir(parents=True, exist_ok=True)

# Okabe-Ito colorblind-safe palette
C_BLUE = "#0072B2"
C_ORANGE = "#E69F00"
C_VERM = "#D55E00"
C_GREEN = "#009E73"
C_PURPLE = "#CC79A7"
C_SKY = "#56B4E9"
C_DARK = "#1F2937"
C_GRAY = "#6B7280"

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 9.5,
        "axes.titlesize": 10.5,
        "axes.labelsize": 9.5,
        "legend.fontsize": 8.5,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.linewidth": 0.8,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def make_fig1_phase_diagram() -> None:
    """Fig 1: Complete Even/Odd Sharp Dimension Thresholds & 11x11 M*=12 Bifurcation."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.0), gridspec_kw={"width_ratios": [1.05, 1.15]})

    # Left panel: N = 4..12 even/odd dichotomy survival vs rupture
    dims = np.array([4, 5, 6, 7, 8, 9, 10, 11, 12])
    parity = ["Even", "Odd", "Even", "Odd", "Even", "Odd", "Even", "Odd", "Even"]
    # Minimum interior return amplitude for minimal-gap-1 spectral-cluster family
    min_vals = []
    for n in dims:
        if n == 4:
            spec = [-1.5, -0.5, 0.5, 1.5]
        elif n == 5:
            spec = [-2.0, -1.0, 0.0, 1.0, 2.0]
        elif n == 6:
            spec = [-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]
        elif n == 7:
            spec = [-3.0, -2.0, -1.0, 0.0, 1.0, 2.0, 3.0]
        elif n == 8:
            spec = [-5.5, -4.5, -3.5, -0.5, 0.5, 3.5, 4.5, 5.5]
        elif n == 9:
            spec = [-22.0, -21.0, -20.0, -1.0, 0.0, 1.0, 20.0, 21.0, 22.0]
        elif n == 10:
            spec = [-8.5, -7.5, -6.5, -5.5, -0.5, 0.5, 5.5, 6.5, 7.5, 8.5]
        elif n == 11:
            spec = [-15.0, -14.0, -13.0, -12.0, -1.0, 0.0, 1.0, 12.0, 13.0, 14.0, 15.0]
        else:
            spec = [-11.5, -10.5, -9.5, -8.5, -7.5, -0.5, 0.5, 7.5, 8.5, 9.5, 10.5, 11.5]
        ch = reconstruct_persymmetric_jacobi(spec)
        ts = np.linspace(0.01, math.pi - 0.05, 4000)
        vals = [return_amplitude(ch, float(t)).real for t in ts]
        min_vals.append(min(vals))

    colors = [C_VERM if v < -1e-4 else (C_BLUE if p == "Odd" else C_GREEN) for v, p in zip(min_vals, parity)]
    ax1.axhline(0.0, color=C_DARK, lw=0.9, ls="--")
    ax1.bar(dims, min_vals, color=colors, width=0.62, edgecolor=C_DARK, linewidth=0.6, zorder=3)
    ax1.set_xticks(dims)
    ax1.set_xlabel(r"Chain length $N$")
    ax1.set_ylabel(r"$\min_{t \in (0,\pi-\delta)} A_N(t)$ (gap-1 cluster family)")
    ax1.set_title(r"(a) Sharp Even ($N_{\mathrm{crit}}^{\mathrm{even}}=8$) & Odd ($N_{\mathrm{crit}}^{\mathrm{odd}}=11$) Rupture")
    ax1.annotate(r"Even rupture" + "\n" + r"$N=8$ (Thm. 5)", xy=(8, min_vals[4]), xytext=(5.8, -0.20),
                 arrowprops={"arrowstyle": "->", "color": C_VERM, "lw": 1.0}, fontsize=8.0, color=C_VERM, ha="center")
    ax1.annotate(r"Critical $N=9$" + "\n" + r"No ESE (Thm. 6)", xy=(9, max(min_vals[5], 0.008)), xytext=(7.2, 0.14),
                 arrowprops={"arrowstyle": "->", "color": C_BLUE, "lw": 1.0}, fontsize=8.0, color=C_BLUE, ha="center")
    ax1.annotate(r"Odd rupture" + "\n" + r"$N=11$ (Thm. 7)", xy=(11, min_vals[7]), xytext=(11.0, 0.14),
                 arrowprops={"arrowstyle": "->", "color": C_VERM, "lw": 1.0}, fontsize=8.0, color=C_VERM, ha="center")
    ax1.set_ylim(-0.34, 0.25)
    ax1.grid(axis="y", alpha=0.25, ls=":")

    # Right panel: 11x11 family S(m) = {0, +-1, +-2m, +-(2m+1), +-(2m+2), +-(2m+3)} for m=1..12
    ms = np.arange(1, 13)
    mins_11 = []
    for m in ms:
        spec = [-2 * m - 3, -2 * m - 2, -2 * m - 1, -2 * m, -1, 0, 1, 2 * m, 2 * m + 1, 2 * m + 2, 2 * m + 3]
        ch = reconstruct_persymmetric_jacobi([float(x) for x in spec])
        ts = np.linspace(0.005, math.pi - 0.15, 5000)
        mins_11.append(min(return_amplitude(ch, float(t)).real for t in ts))
    ax2.axhline(0.0, color=C_DARK, lw=0.9, ls="--")
    ax2.axvline(5.5, color=C_ORANGE, lw=1.2, ls="-.", label=r"Exact threshold $M^* = 2m = 12$ ($m=6$)")
    ax2.plot(ms[:5], mins_11[:5], "o-", color=C_BLUE, lw=1.6, ms=5.5, label=r"Subcritical ($m \leq 5$, SOS $> 0$)")
    ax2.plot(ms[5:], mins_11[5:], "s-", color=C_VERM, lw=1.6, ms=5.5, label=r"Supercritical ($m \geq 6$, ESE $< 0$)")
    ax2.plot([5, 6], [mins_11[4], mins_11[5]], ":", color=C_GRAY, lw=1.1)
    ax2.set_xticks(ms)
    ax2.set_xticklabels([f"{m}\n({2*m})" for m in ms], fontsize=7.5)
    ax2.set_xlabel(r"Cluster parameter $m$ (onset $2m$)")
    ax2.set_ylabel(r"Interior minimum $\min_{t \in (0,\pi-\delta)} A_{11}^{(m)}(t)$")
    ax2.set_title(r"(b) $11 \times 11$ Sharp Integer Bifurcation at $m = 6$ ($M^* = 12$)")
    ax2.legend(frameon=True, facecolor="white", framealpha=0.94, edgecolor="none", loc="lower left", fontsize=7.8)
    ax2.grid(alpha=0.25, ls=":")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_phase_diagram.pdf", bbox_inches="tight")
    plt.close(fig)


def make_fig2_conj41_mechanism() -> None:
    """Fig 2: Conjecture 4.1 (7x7) Forward Divided-Difference Positivity vs Coset-Averaging Converse."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 3.9))

    ts = np.linspace(0.0, math.pi, 1200)
    c_no = reconstruct_persymmetric_jacobi([-3, -2, -1, 0, 1, 2, 3])
    c_no2 = reconstruct_persymmetric_jacobi([-5, -2, -1, 0, 1, 2, 5])
    c_ese = reconstruct_persymmetric_jacobi([-5, -4, -3, 0, 3, 4, 5])
    c_case3 = reconstruct_persymmetric_jacobi([-7, -6, -3, 0, 3, 6, 7])

    ax1.axhline(0.0, color=C_DARK, lw=0.8, ls="--")
    ax1.plot(ts, [return_amplitude(c_no, float(t)).real for t in ts], color=C_BLUE, lw=1.7, label=r"$\{0,\pm 1,\pm 2,\pm 3\}$ (Krawtchouk, No ESE)")
    ax1.plot(ts, [return_amplitude(c_no2, float(t)).real for t in ts], color=C_GREEN, lw=1.4, ls="-.", label=r"$\{0,\pm 1,\pm 2,\pm 5\}$ ($\lambda_1=1$, No ESE)")
    ax1.plot(ts, [return_amplitude(c_ese, float(t)).real for t in ts], color=C_VERM, lw=1.7, label=r"$\{0,\pm 3,\pm 4,\pm 5\}$ (Case 1 ESE)")
    ax1.plot(ts, [return_amplitude(c_case3, float(t)).real for t in ts], color=C_PURPLE, lw=1.5, ls="--", label=r"$\{0,\pm 3,\pm 6,\pm 7\}$ (Case 3 ESE)")
    # Mark coset points for {0, +-3, +-4, +-5}
    for m_idx in range(3):
        tm = (2 * m_idx + 1) * math.pi / 3.0
        if tm < math.pi:
            val = return_amplitude(c_ese, tm).real
            ax1.scatter([tm], [val], color=C_VERM, s=34, zorder=5, edgecolor="white", linewidth=0.5)
    ax1.set_xlim(0, math.pi)
    ax1.set_ylim(-0.72, 1.38)
    ax1.set_xticks([0, math.pi / 3, 2 * math.pi / 3, math.pi])
    ax1.set_xticklabels([r"$0$", r"$\pi/3$", r"$2\pi/3$", r"$\pi$"])
    ax1.set_xlabel(r"Time $t$")
    ax1.set_ylabel(r"Return amplitude $A_7(t)$")
    ax1.set_title(r"(a) Conjecture 4.1 ($7 \times 7$): Real Return Trajectories")
    ax1.legend(frameon=True, facecolor="white", framealpha=0.92, edgecolor="none", loc="upper right", fontsize=7.5)
    ax1.grid(alpha=0.25, ls=":")

    # Right panel: Divided-difference kernel H(w) = sinc^2(sqrt(w)) and secant slope monotonicity
    w = np.linspace(1e-4, 32.0, 800)
    H_w = (1.0 - np.cos(2.0 * np.sqrt(w))) / (2.0 * w)
    w0 = (0.9) ** 2
    H0 = (1.0 - math.cos(2.0 * 0.9)) / (2.0 * w0)
    w_gt = w[w > w0 + 0.05]
    slope = (H0 - ((1.0 - np.cos(2.0 * np.sqrt(w_gt))) / (2.0 * w_gt))) / (w_gt - w0)
    ax2.plot(w, H_w, color=C_BLUE, lw=1.6, label=r"$H(w) = \mathrm{sinc}^2(\sqrt{w})$")
    ax2.plot(w_gt, slope * 2.5, color=C_ORANGE, lw=1.7, ls="-.", label=r"$2.5 \times \frac{H(u^2) - H(w)}{w - u^2}$ (strictly $\downarrow$)")
    ax2.axvline((math.pi / 2) ** 2, color=C_GRAY, lw=0.9, ls=":", label=r"$w = (\pi/2)^2$ (max $u^2$)")
    ax2.set_xlim(0, 30)
    ax2.set_xlabel(r"Squared frequency-time $w = (\lambda u)^2$")
    ax2.set_ylabel(r"Kernel value / scaled secant slope")
    ax2.set_title(r"(b) Strictly Decreasing Secant Slope Behind Thms. 4 & 6")
    ax2.legend(frameon=False, loc="upper right", fontsize=7.8)
    ax2.grid(alpha=0.25, ls=":")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_conj41_mechanism.pdf", bbox_inches="tight")
    plt.close(fig)


def make_fig3_universal_3r2() -> None:
    """Fig 3: Universal (R, r) Phase Transition Map N_crit(R) = 3R + 2."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.0))

    # Left panel: (R, r) grid colored by asymptotic phase (Subcritical, Critical, Supercritical)
    Rs = [2, 3, 4, 5, 6]
    rs = [1, 2, 3, 4, 5, 6, 7]
    grid = np.zeros((len(rs), len(Rs)))
    for i, r in enumerate(rs):
        for j, R in enumerate(Rs):
            if r < R:
                grid[i, j] = 0.0  # Subcritical: Phi -> 0
            elif r == R:
                grid[i, j] = 1.0  # Critical: Phi = 2^{-(R-1)} <= 1/2
            else:
                grid[i, j] = 2.0  # Supercritical: Phi ~ M^{r-R} -> infty

    cmap = matplotlib.colors.ListedColormap(["#DBEAFE", "#FEF3C7", "#FEE2E2"])
    ax1.imshow(grid, origin="lower", cmap=cmap, aspect="auto", extent=[1.5, 6.5, 0.5, 7.5])
    for i, r in enumerate(rs):
        for j, R in enumerate(Rs):
            N = R + 2 * r
            lbl = f"N={N}"
            if r == R + 1 and R <= 5:
                mstar = {2: "7", 3: "12", 4: "30", 5: "78"}[R]
                lbl = f"N={N}\nM*={mstar}"
                col = C_VERM
                wt = "bold"
            elif r == R:
                lbl = f"N={N}\nCrit"
                col = "#B45309"
                wt = "bold"
            elif r < R:
                col = C_BLUE
                wt = "normal"
            else:
                col = C_VERM
                wt = "normal"
            ax1.text(R, r, lbl, ha="center", va="center", fontsize=7.6, color=col, fontweight=wt)

    R_line = np.linspace(1.5, 6.5, 50)
    ax1.plot(R_line, R_line + 0.5, color=C_VERM, lw=1.8, ls="--")
    ax1.set_xticks(Rs)
    ax1.set_yticks(rs)
    ax1.set_xlabel(r"Equidistant Krawtchouk core size $R$")
    ax1.set_ylabel(r"Symmetric cluster pair count $r$")
    ax1.set_title(r"(a) Universal $(R, r)$ Phase Diagram ($N_{\mathrm{crit}} = 3R + 2$ dashed)")

    # Right panel: Asymptotic weight ratio Phi(R, r, M) vs M for R=3 (core {0, +-1})
    Ms = np.linspace(4.0, 60.0, 300)
    for r, col, ls, lbl in [
        (2, C_BLUE, ":", r"$r=2$ ($N=7$, Subcritical $\Phi \propto M^{-1}$)"),
        (3, C_ORANGE, "-.", r"$r=3$ ($N=9$, Critical $\Phi \equiv 1/4$)"),
        (4, C_VERM, "-", r"$r=4$ ($N=11$, Supercritical $\Phi = M/12$)"),
        (5, C_PURPLE, "--", r"$r=5$ ($N=13$, Supercritical $\Phi = M^2/48$)"),
    ]:
        phi = (math.factorial(2) / (math.factorial(r - 1) * (2 ** 2))) * (Ms ** (r - 3))
        ax2.plot(Ms, phi, color=col, ls=ls, lw=1.7, label=lbl)
    ax2.axhline(1.0, color=C_DARK, lw=0.9, ls="--")
    ax2.scatter([12.0], [1.0], color=C_VERM, s=45, zorder=5, edgecolor="white")
    ax2.annotate(r"Exact onset $M^* = 12$", xy=(12.0, 1.0), xytext=(22.0, 0.42),
                 arrowprops={"arrowstyle": "->", "color": C_VERM, "lw": 1.0}, fontsize=8.2, color=C_VERM)
    ax2.set_yscale("log")
    ax2.set_ylim(2e-2, 1e2)
    ax2.set_xlim(4, 60)
    ax2.set_xlabel(r"Cluster scale $M$")
    ax2.set_ylabel(r"Cluster-to-core ratio $\Phi(3, r, M)$")
    ax2.set_title(r"(b) Three-Regime Scaling at $R = 3$ (Theorem 8)")
    ax2.legend(frameon=False, loc="upper left", fontsize=7.5)
    ax2.grid(alpha=0.25, ls=":")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_universal_3r2.pdf", bbox_inches="tight")
    plt.close(fig)


def make_fig4_nonsym_j14() -> None:
    """Fig 4: Theorem 9 Staggered-Field J_{1,4} Complex Amplitude Spiral & Theorem 10B ESE-ETE Duality."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.0))

    ch = reconstruct_persymmetric_jacobi([0.0, 1.0, 4.0, 9.0, 10.0])
    ts = np.linspace(0.0, math.pi, 1600)
    amps = [return_amplitude(ch, float(t)) for t in ts]
    targs = [target_amplitude(ch, float(t)) for t in ts]
    re_a = np.array([z.real for z in amps])
    im_a = np.array([z.imag for z in amps])

    # Left panel: Complex-plane trajectory A(t) in C hitting origin at t = pi/3!
    ax1.axhline(0.0, color=C_GRAY, lw=0.7, ls=":")
    ax1.axvline(0.0, color=C_GRAY, lw=0.7, ls=":")
    ax1.plot(re_a, im_a, color=C_BLUE, lw=1.4, alpha=0.88, label=r"$A(t) = \langle e^{-i J_{1,4} t} e_0, e_0 \rangle \in \mathbb{C}$")
    ax1.scatter([1.0], [0.0], color=C_GREEN, s=55, zorder=5, label=r"$t=0$: $A(0)=1$")
    ax1.scatter([0.0], [0.0], color=C_VERM, s=65, marker="X", zorder=6, label=r"Exact complex ESE $t=\pi/3$: $A(\pi/3)=0$")
    ax1.set_aspect("equal", adjustable="box")
    ax1.set_xlim(-0.78, 1.15)
    ax1.set_ylim(-1.12, 0.72)
    ax1.set_xlabel(r"$\mathrm{Re}\,A(t)$")
    ax1.set_ylabel(r"$\mathrm{Im}\,A(t)$")
    ax1.set_title(r"(a) Complex-Plane Return Trajectory of Staggered $J_{1,4}$ (Thm. 9)")
    ax1.legend(frameon=True, facecolor="white", framealpha=0.92, edgecolor="none", loc="lower left", fontsize=7.5)

    # Right panel: Survival |A(t)|^2, Target |T(t)|^2, ESE-ETE duality, QSL pi/(2 sqrt(15))
    p_ret = np.array([abs(z) ** 2 for z in amps])
    p_tgt = np.array([abs(z) ** 2 for z in targs])
    qsl = math.pi / (2.0 * math.sqrt(15.0))
    ax2.plot(ts, p_ret, color=C_BLUE, lw=1.7, label=r"Return prob. $P_0(t) = |\psi_0(t)|^2$")
    ax2.plot(ts, p_tgt, color=C_ORANGE, lw=1.7, ls="--", label=r"Target prob. $P_4(t) = |\psi_4(t)|^2 = P_0(\pi - t)$")
    ax2.axvline(qsl, color=C_GREEN, lw=1.2, ls=":", label=r"QSL $\tau_{\mathrm{QSL}} = \pi/(2\sqrt{15}) \approx 0.406$")
    ax2.scatter([math.pi / 3.0], [0.0], color=C_VERM, s=55, zorder=5)
    ax2.scatter([2.0 * math.pi / 3.0], [0.0], color=C_PURPLE, s=55, zorder=5)
    ax2.annotate(r"ESE $\tau = \pi/3$", xy=(math.pi / 3.0, 0.02), xytext=(0.76, 0.56),
                 arrowprops={"arrowstyle": "->", "color": C_VERM, "lw": 1.0}, fontsize=8.0, color=C_VERM, ha="center")
    ax2.annotate(r"Dual ETE $2\pi/3$", xy=(2.0 * math.pi / 3.0, 0.02), xytext=(2.36, 0.56),
                 arrowprops={"arrowstyle": "->", "color": C_PURPLE, "lw": 1.0}, fontsize=8.0, color=C_PURPLE, ha="center")
    ax2.set_xlim(0, math.pi)
    ax2.set_ylim(-0.04, 1.06)
    ax2.set_xticks([0, math.pi / 3, 2 * math.pi / 3, math.pi])
    ax2.set_xticklabels([r"$0$", r"$\pi/3$", r"$2\pi/3$", r"$\pi$"])
    ax2.set_xlabel(r"Time $t$")
    ax2.set_ylabel(r"Site probability")
    ax2.set_title(r"(b) Exact PST, ESE–ETE Duality (Thm. 10B) & QSL")
    ax2.legend(frameon=False, loc="upper center", fontsize=7.4)
    ax2.grid(alpha=0.25, ls=":")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig4_nonsym_j14_spiral.pdf", bbox_inches="tight")
    plt.close(fig)


def make_fig5_qgtl_qrng() -> None:
    """Fig 5: Pre-Registered 4-Arm QRNG Static Disorder Study (H1-H3 SIG, H4 Honest Null) & QGTL QSL."""
    data = json.loads((ROOT / "results" / "qgtl_qrng_analysis.json").read_text(encoding="utf-8"))
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.0))

    # Left panel: Paired treatment-vs-control eclipse floor at primary endpoint eps = 0.05
    arms = data["arms"]
    labels = [
        "H1: 7×7\nConj. 4.1\n(p=0.0004)",
        "H2: 8×8\nvs 6×6\n(p=0.0004)",
        "H3: 11×11\nm=6 vs m=5\n(p=0.0008)",
        "H4: 5×5 J₁,₄\nComplex\n(p=0.988 NS)",
    ]
    x = np.arange(len(arms))
    w = 0.35
    treat_med = [a["primary_eps05"]["treat_median"] for a in arms]
    ctrl_med = [a["primary_eps05"]["ctrl_median"] for a in arms]
    treat_iqr = [a["primary_eps05"]["treat_iqr"] / 2.0 for a in arms]
    ctrl_iqr = [a["primary_eps05"]["ctrl_iqr"] / 2.0 for a in arms]

    ax1.bar(x - w / 2, treat_med, w, yerr=treat_iqr, capsize=3, color=C_BLUE, edgecolor=C_DARK, lw=0.6, label="ESE treatment (median ± IQR/2)")
    ax1.bar(x + w / 2, ctrl_med, w, yerr=ctrl_iqr, capsize=3, color=C_ORANGE, edgecolor=C_DARK, lw=0.6, label="No-ESE control (median ± IQR/2)")
    ax1.set_yscale("log")
    ax1.set_ylim(5e-4, 2.5e-1)
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels, fontsize=7.8)
    ax1.set_ylabel(r"Eclipse survival floor $\min |A(t)|$ ($\varepsilon = 0.05$)")
    ax1.set_title(r"(a) Pre-Registered QRNG Study ($n=30$ seeds, Holm FWER)")
    ax1.legend(frameon=False, loc="upper left", fontsize=7.6)
    ax1.grid(axis="y", alpha=0.25, ls=":")

    # Right panel: Disorder scaling log-log across eps = 0.01, 0.02, 0.05, 0.10 for all 4 treatment arms
    eps_vals = [0.01, 0.02, 0.05, 0.10]
    styles = [
        ("H1", C_BLUE, "o-", r"H1 $7\times 7$ ($\beta=0.80$, codim-1)"),
        ("H2", C_GREEN, "s-", r"H2 $8\times 8$ ($\beta=1.08$, codim-1)"),
        ("H3", C_PURPLE, "^-", r"H3 $11\times 11$ ($\beta=0.93$, codim-1)"),
        ("H4", C_VERM, "D--", r"H4 $J_{1,4}$ ($\beta=0.72$, codim-2 null)"),
    ]
    for arm, (_aid, col, fmt, lbl) in zip(arms, styles):
        lvls = {lv["eps"]: lv["treat_median"] for lv in arm["all_levels"]}
        ys = [lvls[e] for e in eps_vals]
        ax2.loglog(eps_vals, ys, fmt, color=col, lw=1.6, ms=5.5, label=lbl)
    ax2.set_xlabel(r"Static QRNG diagonal disorder strength $\varepsilon$")
    ax2.set_ylabel(r"Median perturbed eclipse floor $\min |A_\varepsilon(t)|$")
    ax2.set_title(r"(b) Disorder Scaling: Codim-1 Real vs. Codim-2 Complex Zero")
    ax2.legend(frameon=False, loc="upper left", fontsize=7.6)
    ax2.grid(which="both", alpha=0.22, ls=":")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig5_qgtl_qrng_disorder.pdf", bbox_inches="tight")
    plt.close(fig)


def make_social_preview() -> None:
    """Generate 1280x640 repository social preview card."""
    fig = plt.figure(figsize=(12.8, 6.4), dpi=100, facecolor="#0B1220")
    ax = fig.add_axes((0.05, 0.12, 0.48, 0.62), facecolor="#111B2E")
    ts = np.linspace(0.0, math.pi, 1000)
    c7_no = reconstruct_persymmetric_jacobi([-3, -2, -1, 0, 1, 2, 3])
    c7_ese = reconstruct_persymmetric_jacobi([-5, -4, -3, 0, 3, 4, 5])
    c8_rup = reconstruct_persymmetric_jacobi([-5.5, -4.5, -3.5, -0.5, 0.5, 3.5, 4.5, 5.5])
    ax.axhline(0.0, color="#94A3B8", lw=0.9, ls="--")
    ax.plot(ts, [return_amplitude(c7_no, float(t)).real for t in ts], color="#38BDF8", lw=2.2, label="7×7 No-ESE (Conj. 4.1)")
    ax.plot(ts, [return_amplitude(c7_ese, float(t)).real for t in ts], color="#F97316", lw=2.2, label="7×7 ESE (Coset Avg.)")
    ax.plot(ts, [return_amplitude(c8_rup, float(t)).real for t in ts], color="#F43F5E", lw=2.2, label="8×8 Sharp Rupture")
    ax.set_xlim(0, math.pi)
    ax.set_xticks([0, math.pi / 2, math.pi])
    ax.set_xticklabels(["0", "π/2", "π"], color="#CBD5E1")
    ax.tick_params(colors="#CBD5E1")
    ax.set_ylabel("Return Amplitude A(t)", color="#E2E8F0")
    ax.set_xlabel("Time t ∈ [0, π]", color="#E2E8F0")
    ax.legend(frameon=False, labelcolor="#E2E8F0", loc="upper right", fontsize=9)
    for sp in ("bottom", "left"):
        ax.spines[sp].set_color("#334155")

    fig.text(0.57, 0.78, "SPECTRAL ECLIPSE FRONTIER", color="#38BDF8", fontsize=22, fontweight="bold", family="sans-serif")
    fig.text(0.57, 0.68, "10 Machine-Checked Theorems in Lean 4.35.0\n+ 8-Engine Polyglot & Quantum Verification", color="#F8FAFC", fontsize=14, family="sans-serif")
    bullets = [
        "• Resolves Conjecture 4.1 (arXiv:2507.18767v1) completely",
        "• Sharp Ruptures: N_crit(even) = 8 & N_crit(odd) = 11 (M* = 12)",
        "• Critical 9×9 No-ESE Theorem (19 Bernstein certificates)",
        "• Universal (R, r) Phase Transition: N_crit(R) = 3R + 2",
        "• First Infinite Non-Symmetric Complex ESE Family J_{a,b}",
        "• QGTL Metric g_tt = b_0^2, QSL & Exact ESE-ETE Duality",
        "• AVX2 ASM · C11 · C++20 · Rust · Zig · Eshkol · Moonlab · QGTL/QRNG",
    ]
    fig.text(0.57, 0.22, "\n".join(bullets), color="#CBD5E1", fontsize=11, linespacing=1.65, family="sans-serif")
    fig.text(0.05, 0.87, "Alexander S. Donahue · Independent Researcher · ORCID 0009-0006-8168-9648", color="#94A3B8", fontsize=11, family="sans-serif")
    fig.savefig(MEDIA_DIR / "social-preview.png", dpi=100, facecolor="#0B1220")
    plt.close(fig)


def main() -> int:
    make_fig1_phase_diagram()
    make_fig2_conj41_mechanism()
    make_fig3_universal_3r2()
    make_fig4_nonsym_j14()
    make_fig5_qgtl_qrng()
    make_social_preview()
    print("PASS: Generated 5 vector PDF figures in paper/figures/ and docs/media/social-preview.png.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
