# Pre-Registration Deviations Log (Append-Only — Playbook v1.3 #18)

- **Locked Pre-Registration File:** [`PREREGISTRATION.md`](PREREGISTRATION.md)
- **Root Lock Commit:** `1dac632` (2026-11-26, committed before any `engines/qgtl_qrng` experiment code was compiled or executed)
- **Policy:** `PREREGISTRATION.md` is NEVER edited retroactively. Every deviation, numerical bug fix, or post-registration clarification is appended chronologically below with full before-and-after disclosure.

---

## Deviation #1 (`v1.1.0`, 2026-11-27): Numerical Optimizer Bug Fix in `compute_interior_min` (Endpoint Unchanged)

- **Category:** Numerical implementation bug fix (ZERO change to hypotheses H1–H4, chains, disorder levels $\varepsilon \in \{0.00, 0.01, 0.02, 0.05, 0.10\}$, $K = 30$ paired QRNG seeds, primary window $[0.05\,T_0, 0.95\,T_0]$, permutation test, or Holm–Bonferroni $\alpha = 0.05$ FWER control).
- **Bug Discovered During Cycle 2 Hardening:** In `v1.0.0`, `compute_interior_min` (`engines/qgtl_qrng/se_qgtl_qrng.c`) evaluated $|A(t)|$ on a 500-point uniform grid over $[0.05\,T_0, 0.95\,T_0]$ and ran 50-step golden-section refinement **only around the single lowest grid sample**. Because PST chains satisfy $|A(t)| = O((\pi - t)^{N-1})$ near $t = \pi$, the right-boundary sample $t = 0.95\,\pi$ was occasionally smaller than the discrete 500-point grid sample nearest a sharp interior zero $\tau_{\mathrm{ESE}}$ (spacing $\Delta t = 0.90\pi/500 \approx 5.65 \times 10^{-3}$). Consequently, at $\varepsilon = 0$ (ideal zero-disorder baseline), the `v1.0.0` optimizer trapped on the right boundary $t = 0.95\pi$ and reported $m(J_{1,4}, \varepsilon = 0) = 1.655 \times 10^{-3}$ instead of the exact mathematical value $m(J_{1,4}, 0) = |A(\pi/3)| = 0$.
- **Fix Applied (`v1.1.0`):** `compute_interior_min` still evaluates the exact same 500-point grid on $[0.05\,T_0, 0.95\,T_0]$, but now runs 50-step golden-section refinement on **every local-minimum bracket** ($v_i \le v_{i-1}$ and $v_i \le v_{i+1}$, plus endpoints) and takes the true global minimum over $[0.05\,T_0, 0.95\,T_0]$.
- **Impact Comparison (`v1.0.0` Single-Bracket vs. `v1.1.0` All-Local-Minima-Refined):**

| Arm | Metric | `v1.0.0` (Single-Bracket) | `v1.1.0` (All-Local-Minima Fixed) | Qualitative Verdict Changed? |
| :--- | :--- | :---: | :---: | :---: |
| **H1** ($7\times 7$) | $\varepsilon = 0$ treat min | $8.036 \times 10^{-6}$ | **$0.000 \times 10^{0}$** | Fixed artifact |
| **H1** ($7\times 7$) | $\varepsilon = 0.05$ treat / ctrl med, $d_z$, $\delta$, $p_{\mathrm{Holm}}$ | $0.00233$ / $0.01539$, $+0.91$, $+0.542$, $0.0004$ | $0.00233$ / $0.01539$, $+0.91$, $+0.542$, **$0.0004$** | **No** (SIG) |
| **H2** ($8\times 8$ vs $6\times 6$) | $\varepsilon = 0$ treat min | $7.442 \times 10^{-7}$ | **$0.000 \times 10^{0}$** | Fixed artifact |
| **H2** ($8\times 8$ vs $6\times 6$) | $\varepsilon = 0.05$ treat / ctrl med, $d_z$, $\delta$, $p_{\mathrm{Holm}}$ | $0.00347$ / $0.10373$, $+14.99$, $+1.000$, $0.0004$ | $0.00347$ / $0.10373$, $+14.68$, $+1.000$, **$0.0004$** | **No** (SIG) |
| **H3** ($11\times 11$ $m=6$ vs $5$) | $\varepsilon = 0$ treat min | $5.391 \times 10^{-7}$ | **$0.000 \times 10^{0}$** | Fixed artifact |
| **H3** ($11\times 11$ $m=6$ vs $5$) | $\varepsilon = 0.05$ treat / ctrl med, $d_z$, $\delta$, $p_{\mathrm{Holm}}$ | $0.00752$ / $0.00995$, $+0.75$, $+0.238$, $0.0008$ | $0.00685$ / $0.00995$, $+0.83$, $+0.247$, **$0.0004$** | **No** (SIG, stronger) |
| **H4** ($5\times 5$ $J_{1,4}$ vs Kraw.) | $\varepsilon = 0$ treat min | $1.655 \times 10^{-3}$ | **$0.000 \times 10^{0}$** | Fixed artifact |
| **H4** ($5\times 5$ $J_{1,4}$ vs Kraw.) | $\varepsilon = 0.05$ treat / ctrl med, $d_z$, $\delta$, $p_{\mathrm{Holm}}$ | $0.01626$ / $0.01377$, $+0.00$, $-0.078$, $0.9880$ | $0.01626$ / $0.01377$, $+0.00$, $-0.078$, **$0.9855$** | **No** (Honest NULL) |

- **Conclusion:** Fixing the optimizer bug eliminates all four $\varepsilon = 0$ discretization artifacts cleanly without altering a single pre-registered hypothesis decision (H1–H3 remain strongly significant at $p_{\mathrm{Holm}} = 0.0004$; H4 remains a clean pre-registered null at $p_{\mathrm{Holm}} = 0.9855$).
