# ADR-0004: Pre-Registered Four-Arm QRNG Disorder Study and Honest Null Reporting

- **Status:** Accepted
- **Date:** 2026-11-26
- **Author:** Alexander Stephen Donahue

## Context

In physical quantum spin-chain realizations, manufacturing tolerances introduce diagonal on-site field disorder $\delta h_j$. Testing whether exact ESE crossings survive realistic disorder is vulnerable to p-hacking, seed cherry-picking, or hiding negative results if the protocol is not fixed before running experiments.

## Decision

1. **Git-Committed Pre-Registration (`B32`):** Commit `PREREGISTRATION.md` in the root commit `1dac632` specifying all four paired treatment-vs-control arms (H1: $7\times 7$, H2: $8\times 8$ vs $6\times 6$, H3: $11\times 11$ $m=6$ vs $m=5$, H4: $5\times 5$ complex $J_{1,4}$ vs $5\times 5$ Krawtchouk), fixed disorder grid $\varepsilon \in \{0, 0.01, 0.02, 0.05, 0.10\}$ with primary endpoint $\varepsilon = 0.05$, 30 deterministic QRNG seeds (`engines/qgtl_qrng`), two-sided 10,000-sign-flip paired permutation tests (`B29`), Cohen's $d_z$, Cliff's $\delta$, 10,000-resample 95% bootstrap CIs (`B30`), and step-down Holm–Bonferroni FWER control at $\alpha = 0.05$ (`B31`). Any post-registration bug fix (such as Deviation #1 in `v1.1.0`) is logged append-only in `DEVIATIONS.md` while keeping `PREREGISTRATION.md` untouched.
2. **Honest Reporting of All Outcomes:** Report every pre-registered arm verbatim in `results/qgtl_qrng_analysis.json`, `paper/main.tex`, `CLAIMS.md`, and `LIMITATIONS.md`, regardless of significance.

## Consequences

- **Positive:** Discovered a genuine physical distinction between **codimension-1 real crossings** (H1–H3, all highly significant $p_{\text{Holm}} = 0.0004$, topologically robust to diagonal disorder) and **codimension-2 complex zeros** (H4, pre-registered null $p_{\text{Holm}} = 0.9855$, $d_z = 0.00$, generically lifted by real diagonal perturbations). Preserving this honest null strengthens scientific credibility and explains a fundamental geometric feature of complex ESE.
- **Trade-off:** None — transparency is strictly superior to post-hoc filtering.
