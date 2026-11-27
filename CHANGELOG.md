# Changelog

All notable changes to `spectral-eclipse-frontier` are documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/) and [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

*No unreleased changes.*

## [1.1.0] - 2026-11-27

### Added
- **3-Cycle Deep Adversarial Hardening (`v1.1.0`)**: Full-repository file-by-file, line-by-line audit against Build Standard v1.2.0 and Defensible Independent AI Research Playbook v1.3 (`HARDENING_INDEX.md`, `HARDENING_LOG.md`, `docs/reviews/cycle{1,2,3}-v1.1.md`, `docs/reviews/ten-pass-audit.md`).
- **Lean 4 Non-Vacuity & Hard CI Gates**: Added 3 concrete `NonVacuity` witnesses (`witness_7x7_unreduced_c2_3_6_9`, `witness_universal_3R_plus_2_R3`, `witness_J14_ese_ete_duality`, raising coverage from 15 to 18 witnesses and total audited theorems from 568 to **572** with 52 explicit `#print axioms`); promoted `lake exe runLinter SpectralEclipse Solution` to a **hard zero-error CI gate**; added a **live `sorry`-tamper negative comparator CI gate** in `.github/workflows/lean-verify.yml`.
- **Playbook v1.3 & Build Standard v1.2.0 Artifacts**: Created append-only `DEVIATIONS.md` (Playbook #18), dated `docs/literature-search.md` (Playbook #15), `scripts/generate_llms_full.py` (`A32` deterministic generator), `web/observatory.js` (external module enabling strict CSP `script-src 'self'`), and Software Heritage `swh:` identifier in `CITATION.cff` (#30).
- **Public API Constants & Expanded Verification Suite**: Exported `FLOAT64_CANCELLATION_MARGIN` and `FLOAT64_MIN_RE_THRESHOLD` in `python/spectral_eclipse`; expanded `tests/test_all.py` from 15 to **22 tests** covering version parity across all 8 manifests, `repo.yaml` JSON Schema validation, zero broken relative links, zero stale identifiers, manifest tamper rejection, and exact `eps = 0` QRNG ground-state checks.

### Changed
- **Dependency Security Remediation (0 CVEs)**: Removed unused `PyMuPDF` from `requirements.txt`, upgraded `pillow==13.0.0` and `pytest==9.2.0`, and pinned `pygments==2.21.0` — resolving all 62 GitHub Dependabot alerts and all 65 `osv-scanner` advisories.
- **Crossref Retraction Verification**: Upgraded `scripts/check_citations.py` to enforce Crossref `update-to`/`updated-by` retraction checks and title word-overlap verification (`>= 0.50`) across all 15 bibliography entries.
- **GitHub Pages Web Observatory (`web/index.html`, `web/observatory.js`)**: Removed `'unsafe-inline'` from `script-src`, added WCAG 2.2 AA skip-navigation link and `aria-live="polite"` readout, and synchronized counts (`572` theorems, `v1.1.0`, `0TH-2026-024`).

### Fixed
- **QRNG Interior-Minimum Optimizer Bug (Deviation #1, `engines/qgtl_qrng/se_qgtl_qrng.c`)**: Replaced single-bracket golden-section refinement in `compute_interior_min` with all-local-minimum bracket refinement on the identical 500-point grid, eliminating boundary trapping that previously gave $m(J_{1,4}, \varepsilon=0) = 1.655 \times 10^{-3}$ instead of exact $0.000$. Re-ran the 30-seed study (`results/qgtl_qrng_study.json`, `results/qgtl_qrng_analysis.json`, Figure 5, Table 4): all four primary conclusions remain identical (H1–H3 significant at $p_{\mathrm{Holm}} = 0.0004$; H4 clean null at $p_{\mathrm{Holm}} = 0.9855$). Logged transparently in `DEVIATIONS.md` while keeping `PREREGISTRATION.md` untouched.
- **C11 Error Handling & Resource Safety**: Propagated OOM and zero-norm status codes in `bessel_j_array` (`engines/c/se_core.c`); fixed `FILE *` leak on `qrng_init` failure and checked all `tridiag_ql_c` return codes in `engines/qgtl_qrng/se_qgtl_qrng.c`.
- **Lean Batteries Linter, Ruff EXE001, & Mypy Strict**: Added missing docstring to `hochstadtWeightOdd` (`lean/SpectralEclipse/Defs.lean`), fixed `TypedDict` typing in `scripts/build_blueprint.py`, split `ruff` and `mypy --strict` into distinct visible CI steps, and set executable permissions (`100755`) on all shebang Python scripts (fixing all 13 Linux CI `ruff EXE001` failures).
- **Manuscript & Documentation Factual Corrections**: Fixed `paper/main.tex` Bernstein domain bound (`4.5^2` -> `5.5^2` matching `TrigBounds.lean`), restored average-hopping factor $\bar{b}$ in the disorder Hamiltonian $J_\varepsilon = J + \varepsilon \bar{b}\,\mathrm{diag}(\xi)$, fixed `Challenge.lean` line count (`280` -> `290`), fixed Mega-Atlas count (`0/1,900` -> `0/2,000`), fixed swapped H2/H3 entries and CLI flag in `docs/run-log.md`, fixed hallucinated Python/Lean symbol names in `UPGRADING.md` and `docs/verification.md`, replaced `Rayon` with `std::thread`, and standardized Master Archive ID to `0TH-2026-024`.

## [1.0.0] - 2026-11-26

### Added
- **Lean 4.35.0 Formal Proof Library (`lean/SpectralEclipse/`)**: Machine-checked, sorry-free proofs of all 10 linked theorems in quantum spin-chain Early State Exclusion (ESE), including complete resolution of Conjecture 4.1 of Escobar-Garcia-Minenkova (arXiv:2507.18767v1) for $7\times 7$ symmetric PST chains, complete $4\times 4$, $5\times 5$, and $6\times 6$ dichotomies, the $9\times 9$ critical no-ESE theorem, sharp rupture thresholds $N_{\mathrm{crit}}^{\mathrm{even}} = 8$ and $N_{\mathrm{crit}}^{\mathrm{odd}} = 11$ ($M^* = 12$), universal $(R, r)$ phase boundary $N_{\mathrm{crit}}(R) = 3R + 2$, the infinite non-symmetric staggered-field $5\times 5$ complex-amplitude ESE family $J_{a,b}$ verified directly via literal matrix eigenpairs, and the exact QGTL / Mandelstam-Tamm lower bound $\tau_{\mathrm{ESE}} \ge \pi/(2 b_0)$ plus ESE-ETE duality.
- **Palomar 6-Kernel Isolation (`lean/Challenge.lean`, `lean/Solution.lean`, `lean/comparator.json`, `lean/VerifyAxioms.lean`)**: Standalone Mathlib-only target specifications, exhaustive `Lean.collectAxioms` audit, non-vacuity witnesses, adversarial refutations, and live negative kernel rejection tests.
- **8 Independent Computational & Quantum Engines (`engines/`)**: NASM x86-64 AVX2+FMA SpMV/Chebyshev kernel, ISO C11 Hochstadt/Sturm verifier, C++20 direct complex matrix-exponential propagator, Rust parallel multi-core spectral phase scanner (`#![forbid(unsafe_code)]`), Zig 0.17.0 arbitrary-precision rational (`std.math.big.int`) Hochstadt reconstructor, Eshkol v1.3.6 forward-mode dual-number automatic differentiation oracle, Moonlab WASM full $2^5 = 32$-dimensional multi-qubit XY simulator, and QGTL + Quantum-RNG speed-limit and pre-registered disorder-robustness engine.
- **Pre-Registered Statistical Study (`PREREGISTRATION.md`)**: Locked prior to execution; 30-seed QRNG diagonal-disorder comparison across subcritical, critical, rupture, and staggered non-symmetric chains using paired exact permutation tests, Holm-Bonferroni correction, and 10,000-resample bootstrap 95% CIs.
- **AMS-LaTeX White Paper & Figures (`paper/`, `dist/`)**: Publication-grade preprint with 5 vector PDF figures, zero overfull hboxes, 100% live Crossref/arXiv-verified bibliography, standalone `arxiv_submission.tar.gz`, interactive GitHub Pages Observatory & Lean Blueprint (`web/`), RFC 3161 + OpenTimestamps provenance (`data/MANIFEST.sha256.{tsr,ots}`), and 3-cycle adversarial hardening log (`HARDENING_LOG.md`).
