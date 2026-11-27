# Limitations, Scope Boundaries, and Epistemic Honesty

## 1. Formal Proof Boundary vs. Computational & Empirical Scope

- **Machine-Checked in Lean 4.35.0 (`[LEAN-6K]`):** Theorems 1–10 (all 12 isolated targets in `lean/Challenge.lean`, 15 non-vacuity witnesses, and 5 adversarial refutations; 572 audited theorem constants strictly within `[propext, Classical.choice, Quot.sound]`).
- **Exact Computational (`[EXACT-COMP]`):** Finite-$M$ critical rupture thresholds for higher Krawtchouk cores $R=4$ ($N=14, M^*=30$) and $R=5$ ($N=17, M^*=78$) are verified by multi-core Rust, C++20, and SymPy rather than Lean 4 kernel certificates.
- **Empirical (`[EMPIRICAL]`):** The 4-arm QRNG static-disorder robustness study (`PREREGISTRATION.md`, `results/qgtl_qrng_analysis.json`) is a finite-sample ($K=30$ paired seeds per arm) empirical simulation under uniform static diagonal disorder $\varepsilon \in [0, 0.10]$. It does not prove analytical disorder thresholds for arbitrary noise models (e.g., off-diagonal coupling jitter or time-dependent dephasing).

## 2. Honest Pre-Registered Null Result (Hypothesis H4)

In the pre-registered QRNG study locked in root commit `1dac632`, Arm H4 tested whether the non-symmetric staggered-field complex ESE chain $J_{1,4}$ maintains a deeper eclipse floor under $\varepsilon = 0.05$ static diagonal disorder than the $5\times 5$ Krawtchouk control. **H4 returned a clean null result** (`treat_median = 0.01626` vs. `ctrl_median = 0.01377`, `mean_diff = +0.00006`, 95% bootstrap CI `[-0.00621, +0.00689]`, Cohen's $d_z = 0.00$, $p_{\mathrm{Holm}} = 0.988$). This reflects genuine topological physics: a complex zero in $\mathbb{C}$ is codimension-2 and lifts linearly as $O(\varepsilon)$, whereas real sign changes in symmetric chains (H1–H3, all $p_{\mathrm{Holm}} \le 0.0008$) are topologically protected codimension-1 crossings on $\mathbb{R}$.

## 3. Review, Authorship, and AI Transparency

- This work is an **unrefereed research preprint** (`v1.0.0`). It has not been externally peer-reviewed or submitted to a journal, arXiv, Zenodo, or the Palomar Registry.
- Analytical derivation, Lean 4.35.0 proof engineering, polyglot verification scripts, and manuscript drafting were AI-assisted (Google Gemini / Antigravity) under sole human direction and audit oversight (Alexander S. Donahue, ORCID `0009-0006-8168-9648`).
- Independent human line-by-line review of all 12 Lean files and external independent operator replication (`B44`) remain **OPEN**.
- **Mega-Atlas Boundary:** `0 / 1,900` Mega-Atlas grand problems are retired or claimed (`docs/MEGA_ATLAS_CROSSCHECK.md`). The resolved published conjecture is Conjecture 4.1 of Escobar, Garcia, and Minenkova (`arXiv:2507.18767v1`).

## 4. Real vs. Metaphor

- **"Spectral Eclipse"** is a descriptive metaphor for the strictly defined mathematical predicate **Early State Exclusion (ESE)**: $\exists \tau \in (0, T_0)$ such that $\langle e_0, e^{-iJt} e_0 \rangle = 0$.
- **"Rupture"** and **"Phase Transition"** denote exact mathematical transitions in the sign of $A_N(t)$ and the asymptotic scaling exponent of the cluster-to-core Hochstadt weight ratio $\Phi(R, r, M) \propto M^{r-R}$ at $r = R+1$; no thermodynamic limit in physical particle number is claimed.
- **Quantum-RNG (`third_party/quantum_rng`)** is a deterministic software CSPRNG/quantum-inspired entropy engine tested against NIST statistical suites, not a live physical optical beam-splitter hardware device.
