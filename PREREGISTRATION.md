# Pre-Registration: Seeded QRNG Diagonal-Disorder Robustness of Early State Exclusion

- **Document status:** Locked prior to running the disorder Monte Carlo experiment (Build Standard v1.2.0 item B32).
- **Author:** Alexander S. Donahue (ORCID `0009-0006-8168-9648`, Independent Researcher, Spokane, WA, USA)
- **Date locked:** 2026-11-26 (committed to `main` before any `engines/qgtl_qrng` experiment code is compiled or executed).
- **Epistemic tag:** `[NUM-APPROX]` (experimental statistical robustness study; completely separate from our exact `[LEAN-6K]` theorems).

## 1. Research Question

Exact Early State Exclusion (ESE) is an exact zero $\mathcal{A}(\tau) = \langle e^{-i J \tau} \mathbf{e}_0, \mathbf{e}_0 \rangle = 0$ at an interior time $\tau \in (0, T_0)$ for an ideal persymmetric Jacobi spin chain $J$. Under realistic fabrication noise (zero-mean random static on-site diagonal disorder $J_\varepsilon = J + \varepsilon \operatorname{diag}(\xi_0, \dots, \xi_{N-1})$ with $\xi_k \sim \mathrm{Uniform}(-1, 1)$ drawn from the vendored Tsotchke Quantum-RNG stream `third_party/quantum_rng/`), exact zeros lift into nonzero return-probability minima
$$m(J_\varepsilon) := \min_{t \in [0.05 T_0, 0.95 T_0]} \left| \langle e^{-i J_\varepsilon t} \mathbf{e}_0, \mathbf{e}_0 \rangle \right|.$$
We test whether genuine **rupture / staggered ESE chains** retain strictly deeper interior amplitude eclipses under diagonal disorder than **no-ESE control chains** of identical or matched dimension and identical spectral bandwidth normalization.

## 2. Primary Endpoints & Arms (Fixed Before Execution)

Every chain is normalized by its Frobenius spectral radius scale so the perturbation ratio $\varepsilon \in \{0.00, 0.01, 0.02, 0.05, 0.10\}$ is dimensionless relative to the chain's average hopping strength $\bar{b} = \frac{1}{N-1}\sum_{k=0}^{N-2} b_k$.

Four pre-specified comparisons (paired on identical QRNG seed $s \in \{1, 2, \dots, 30\}$, with $N_{\mathrm{seeds}} = 30$ independent paired replicates per disorder level $\varepsilon$, using 500-point interior grid refined by golden-section search):

1. **H1 (7x7 Conjecture 4.1 Dichotomy — Rupture vs. Control, $N = 7$):**
   - *Treatment (ESE):* $7\times 7$ coprime chain $\{0, \pm 3, \pm 4, \pm 5\}$ (minimal odd coprime ESE witness, $\lambda_1 = 3 \nmid 4, 5$).
   - *Control (No ESE):* $7\times 7$ divisibility chain $\{0, \pm 1, \pm 2, \pm 5\}$ ($\lambda_1 = 1$, proven no ESE by Theorem 4).
   - *Directional hypothesis:* At $\varepsilon = 0.05$, median $m_{\mathrm{treat}} < m_{\mathrm{ctrl}}$ (strictly deeper return-amplitude minimum).
2. **H2 (8x8 Sharp Even Rupture vs. 6x6 Even Critical Control):**
   - *Treatment (ESE):* $8\times 8$ minimal even rupture chain $\{\pm\frac{1}{2}, \pm\frac{7}{2}, \pm\frac{9}{2}, \pm\frac{11}{2}\}$ ($p_1 = 1$, Theorem 5).
   - *Control (No ESE):* $6\times 6$ even critical chain $\{\pm\frac{1}{2}, \pm\frac{5}{2}, \pm\frac{7}{2}\}$ ($p_1 = 1$, Theorem 3).
   - *Directional hypothesis:* At $\varepsilon = 0.05$, median $m_{\mathrm{treat}} < m_{\mathrm{ctrl}}$.
3. **H3 (11x11 Exact Threshold $M^* = 12$ — Supercritical $m=6$ vs. Subcritical $m=5$):**
   - *Treatment (ESE):* $11\times 11$ supercritical chain $\{0, \pm 1, \pm 12, \pm 13, \pm 14, \pm 15\}$ ($m = 6$, Theorem 7).
   - *Control (No ESE):* $11\times 11$ subcritical chain $\{0, \pm 1, \pm 10, \pm 11, \pm 12, \pm 13\}$ ($m = 5$, Theorem 7).
   - *Directional hypothesis:* At $\varepsilon = 0.05$, median $m_{\mathrm{treat}} < m_{\mathrm{ctrl}}$.
4. **H4 (5x5 Staggered Non-Symmetric Complex ESE $J_{1,4}$ vs. 5x5 Krawtchouk Control):**
   - *Treatment (Complex ESE):* $5\times 5$ staggered non-symmetric chain $J_{1,4}$ with spectrum $\{0, 1, 4, 9, 10\}$ (Theorem 9, exact complex eclipse at $\tau = \pi/3$).
   - *Control (No ESE):* $5\times 5$ symmetric equidistant Krawtchouk chain $\{0, \pm 1, \pm 2\}$ (Theorem 2, proven no ESE).
   - *Directional hypothesis:* At $\varepsilon = 0.05$, median $m_{\mathrm{treat}} < m_{\mathrm{ctrl}}$.

## 3. Fixed Statistical Analysis Plan

- **Sample size:** $K = 30$ paired QRNG seeds (`seed = 1..30`) per comparison (each seed draws fresh independent disorder vectors via `quantum_rng` SHA-256/ChaCha-mixed deterministic entropy stream).
- **Primary test:** Two-sided exact / $10{,}000$-sign-flip paired permutation test on $d_s = m_{\mathrm{ctrl}}(s) - m_{\mathrm{treat}}(s)$ at $\varepsilon = 0.05$.
- **Multiple-comparison correction:** Holm-Bonferroni across the family of $4$ primary hypotheses ($\alpha_{\mathrm{FWER}} = 0.05$).
- **Effect sizes & uncertainty:** Report median difference, Hodges-Lehmann / mean difference, Cohen's $d_z$ (paired), Cliff's $\delta$, and 10,000-resample percentile bootstrap 95% confidence intervals.
- **No p-hacking / stopping rules:** All 4 comparisons and all 5 disorder levels $\varepsilon \in \{0.00, 0.01, 0.02, 0.05, 0.10\}$ will be reported in full regardless of outcome, including any null or reversed effects.
- **Secondary exploratory metric (labeled exploratory):** Return-probability scaling $m(\varepsilon) \propto \varepsilon^\beta$ and QGTL speed-limit ratio $\eta(\varepsilon) = \frac{\pi}{2 b_0 \tau_{\min}(\varepsilon)}$.
