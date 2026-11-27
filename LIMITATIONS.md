# Limitations, Scope Boundaries, and Epistemic Honesty

## 1. Formal Proof Boundary vs. Computational & Empirical Scope

- **Machine-Checked in Lean 4.35.0 (`[LEAN-6K]`):** Theorems 1–10 (all 12 isolated targets in `lean/Challenge.lean`, 18 non-vacuity witnesses, and 5 adversarial refutations; **572 audited theorem constants** strictly within `[propext, Classical.choice, Quot.sound]`, zero Batteries `runLinter` errors, and a live `sorry`-tamper negative comparator CI gate).
- **Exact Computational (`[EXACT-COMP]`):** Finite-$M$ critical rupture thresholds for higher Krawtchouk cores $R=4$ ($N=14, M^*=30$) and $R=5$ ($N=17, M^*=78$) are verified by multi-core Rust (`std::thread`), C++20, and SymPy rather than Lean 4 kernel certificates.
- **Empirical (`[EMPIRICAL]`):** The 4-arm QRNG static-disorder robustness study (`PREREGISTRATION.md`, `DEVIATIONS.md`, `results/qgtl_qrng_analysis.json`) is a finite-sample ($K=30$ paired seeds per arm) empirical simulation under uniform static diagonal disorder $\varepsilon \in [0, 0.10]$ scaled by mean hopping $\bar{b}$. It does not prove analytical disorder thresholds for arbitrary noise models (e.g., off-diagonal coupling jitter or time-dependent dephasing).

## 2. Honest Pre-Registered Null Result (Hypothesis H4) & Deviation #1

In the pre-registered QRNG study locked in root commit `1dac632`, Arm H4 tested whether the non-symmetric staggered-field complex ESE chain $J_{1,4}$ maintains a deeper eclipse floor under $\varepsilon = 0.05$ static diagonal disorder than the $5\times 5$ Krawtchouk control. Following the `v1.1.0` optimizer fix documented in `DEVIATIONS.md` (which eliminated boundary trapping at $\varepsilon = 0$ so all four arms evaluate to exact $0.000$ in the clean limit), **H4 remains a clean null result** (`treat_median = 0.01626` vs. `ctrl_median = 0.01377`, `mean_diff = +0.00007`, 95% bootstrap CI `[-0.00619, +0.00689]`, Cohen's $d_z = 0.00$, Cliff's $\delta = -0.078$, $p_{\mathrm{Holm}} = 0.9855$). This reflects genuine topological physics: a complex zero in $\mathbb{C}$ is codimension-2 and lifts linearly as $O(\varepsilon)$ ($\beta \approx 0.83$), whereas real sign changes in symmetric chains (H1–H3, all $p_{\mathrm{Holm}} = 0.0004$) are topologically protected codimension-1 crossings on $\mathbb{R}$.

## 3. Review, Authorship, Conflict of Interest, and Export Control

- **Preprint Status:** This work is an **unrefereed research preprint** (`v1.1.0`). It has not been externally peer-reviewed or submitted to a journal, arXiv, Zenodo, or the Palomar Registry.
- **AI Transparency:** Analytical derivation, Lean 4.35.0 proof engineering, polyglot verification scripts, and manuscript drafting were AI-assisted (Google Gemini / Antigravity) under sole human direction and audit oversight (Alexander S. Donahue, Independent Researcher, ORCID `0009-0006-8168-9648`).
- **Open Human Verification:** Independent human line-by-line review of all 12 Lean files and external independent operator replication (`B44`) remain **OPEN**.
- **Mega-Atlas Boundary:** `0 / 2,000` Mega-Atlas grand problems are retired or claimed (`docs/MEGA_ATLAS_CROSSCHECK.md`). The resolved published conjecture is Conjecture 4.1 of Escobar, Garcia, and Minenkova (`arXiv:2507.18767v1`).
- **Conflict of Interest & Funding:** The author declares no competing financial or non-financial interests; this is self-funded independent research.
- **Export-Control Self-Screen:** This repository contains fundamental mathematical research in spectral theory and linear algebra intended for open scientific dissemination and falls within the fundamental research exclusion of 15 CFR 734.8. It contains no cryptographic primitives, weapons/munitions models, or export-controlled hardware designs.

## 4. Real vs. Metaphor

- **"Spectral Eclipse"** is a descriptive metaphor for the strictly defined mathematical predicate **Early State Exclusion (ESE)**: $\exists \tau \in (0, T_0)$ such that $\langle e_0, e^{-iJt} e_0 \rangle = 0$.
- **"Rupture"** and **"Phase Transition"** denote exact mathematical transitions in the sign of $A_N(t)$ and the asymptotic scaling exponent of the cluster-to-core Hochstadt weight ratio $\Phi(R, r, M) \propto M^{r-R}$ at $r = R+1$; no thermodynamic limit in physical particle number is claimed.
- **Quantum-RNG (`third_party/quantum_rng`)** is a deterministic software CSPRNG/quantum-inspired entropy engine tested against NIST statistical suites, not a live physical optical beam-splitter hardware device.
