# Roadmap

## v1.0.0 (Current Release — November 2026)

- [x] Machine-checked Lean 4.35.0 proofs (6-kernel Palomar verified) of the complete 10-theorem Early State Exclusion (ESE) chain:
  - Complete $4\times 4$, $5\times 5$, $6\times 6$, and $7\times 7$ (Conjecture 4.1 of Escobar-Garcia-Minenkova, arXiv:2507.18767v1) dichotomies.
  - Exact critical no-ESE theorem for $9\times 9$ ($\lambda_1 = 1$).
  - Sharp rupture dimensions $N_{\mathrm{crit}}^{\mathrm{even}} = 8$ and $N_{\mathrm{crit}}^{\mathrm{odd}} = 11$ with exact integer threshold $M^* = 12$.
  - Universal $(R, r)$ Krawtchouk-core vs. spectral-cluster phase transition at $N_{\mathrm{crit}}(R) = 3R + 2$.
  - First infinite non-symmetric staggered-field complex-amplitude ESE family $J_{a,b}$ ($5\times 5$, exact vanishing at $\tau = \pi/3$).
  - Exact QGTL Fubini-Study / Mandelstam-Tamm lower bound $\tau_{\mathrm{ESE}} \ge \pi/(2b_0)$ and ESE-ETE duality.
- [x] 8-engine polyglot verification observatory (NASM AVX2, ISO C11, C++20, Rust, Zig BigInt, Eshkol AD, Moonlab WASM $2^N$ XY simulator, QGTL + QRNG).
- [x] Pre-registered 30-seed QRNG disorder-robustness study with paired permutation tests and Holm-Bonferroni correction.
- [x] Publication-grade AMS-LaTeX white paper (`dist/Donahue_2026_spectral_eclipse_frontier.pdf`), standalone `arxiv_submission.tar.gz`, interactive GitHub Pages Observatory & Lean Blueprint, dual RFC 3161 + OpenTimestamps proof-of-existence, and 3-cycle adversarial hardening audit.

## v1.1.0 (Planned Follow-Up Research)

- Complete analytic converse classification for $9\times 9$ symmetric PST chains when $\lambda_1 \ge 3$ and $\gcd(\lambda_1,\lambda_2,\lambda_3,\lambda_4) = 1$ (currently verified computationally with zero counterexamples; proving all divisibility subcases analytically is a natural next theorem).
- Analytic proof (or counterexample) for non-symmetric $4\times 4$ PST chains (currently 0 ESE instances found across all exhaustive odd-gap scans up to gap 31).
- Extension of the staggered-field complex-amplitude family $J_{a,b}$ to higher odd lengths $N = 7, 9, \dots$ and arbitrary non-persymmetric asymmetric-coupling spin networks.
- External submission to arXiv (`quant-ph` / `math.SP`) subject to standard endorsement and human refereeing.
