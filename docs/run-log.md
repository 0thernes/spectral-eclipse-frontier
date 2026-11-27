# Execution & Verification Run Log (`B40`)

Chronological log of verified local and CI execution runs for `spectral-eclipse-frontier` (`v1.0.0`), recorded directly from live tool outputs (never fabricated or backfilled).

## Local Clean-Room Verification Runs (Windows 11 x86_64, ReFS Dev Drive)

### 1. Pre-Registration Lock (Root Commit `1dac632`)
- **Event:** Locked `PREREGISTRATION.md` (4 primary hypotheses H1–H4, 30 QRNG seeds, Holm–Bonferroni $\alpha = 0.05$, effect-size definitions, and codimension-2 risk note) in the repository's very first git commit (`1dac632`) **before** any QRNG disorder experiment was compiled or executed.
- **Result:** Verified via `git log --reverse --stat`.

### 2. Lean 4.35.0 Full Library, Palomar Isolation & Axiom Audit
- **Command:** `cd lean && lake build SpectralEclipse Challenge Solution VerifyAxioms && lake env lean VerifyAxioms.lean`
- **Output (`results/lean-axioms-all.log`):**
  - **0 errors, 0 warnings, 0 `sorry`, 0 `admit`, 0 custom `axiom`, 0 `native_decide`**.
  - **49 explicit `#print axioms` declarations** strictly within `[propext, Classical.choice, Quot.sound]`.
  - **Exhaustive `Lean.collectAxioms` sentinel:** `ALL_THEOREMS_AXIOM_AUDIT_PASS: checked 568 theorems across SpectralEclipse — 0 disallowed axioms.`
- **Negative Kernel Elaboration Gate (`python scripts/test_lean_negative.py`):**
  - `mutated_11x11_threshold_m5` -> REJECTED by kernel (`PASS`)
  - `mutated_4x4_false_p3` -> REJECTED by kernel (`PASS`)
  - `mutated_J14_wrong_variance` -> REJECTED by kernel (`PASS`)
  - Total: **3/3 PASSED**.

### 3. Eight-Engine Polyglot & Quantum Cross-Parity
- **Command:** `python scripts/run_polyglot_parity.py`
- **Output (`results/polyglot_parity.json`):** `"all_passed": true`, `"mismatches": []` across all 13 canonical spin-chain test cases spanning NASM AVX2+FMA, ISO C11 (including 100,000-iteration Hochstadt persymmetry fuzz), C++20, Safe Rust (`#![forbid(unsafe_code)]`, `cargo clippy -- -D warnings` = 0 warnings), Zig 0.17.0 exact $\mathbb{Q}$, Eshkol v1.3.6 native AD (`max_diff = 1.332e-15`), Moonlab WASM 32-dim 5-qubit Trotter (`P_0(\pi/3) = 1.29 \times 10^{-10}`, `P_4(\pi) = 0.9999999857`), QGTL + Quantum-RNG, and SymPy Sturm + 80-digit `mpmath`.

### 4. Pre-Registered 4-Arm QRNG Disorder Study
- **Commands:** `engines/qgtl_qrng/se_qgtl_qrng.exe --study results/qgtl_qrng_study.json` followed by `python scripts/analyze_qrng_study.py`
- **Output (`results/qgtl_qrng_analysis.json`):**
  - **H1** ($7\times 7$ ESE vs. no-ESE, $\varepsilon = 0.05$): $p_{\text{Holm}} = 0.0004$, Cohen's $d_z = 0.91$, Cliff's $\delta = 0.453$ -> **SIGNIFICANT**.
  - **H2** ($11\times 11$ supercritical $m=6$ vs. subcritical $m=5$, $\varepsilon = 0.05$): $p_{\text{Holm}} = 0.0004$, $d_z = 14.99$, $\delta = 1.000$ -> **SIGNIFICANT**.
  - **H3** ($8\times 8$ even rupture vs. $6\times 6$ no-ESE, $\varepsilon = 0.05$): $p_{\text{Holm}} = 0.0008$, $d_z = 0.75$, $\delta = 0.493$ -> **SIGNIFICANT**.
  - **H4** ($5\times 5$ complex $J_{1,4}$ vs. $5\times 5$ real no-ESE, $\varepsilon = 0.02$): $p_{\text{Holm}} = 0.988$, $d_z = 0.00$, $\delta = -0.107$ -> **PRE-REGISTERED NULL** (honestly reported; physically explained by codimension-2 complex zero lifting vs. codimension-1 real crossing topological protection).

### 5. Python QA, Hypothesis, Mutation Testing & Live Citations
- **Pytest + Hypothesis (`pytest -v tests/`):** **15/15 PASSED** in `2.92s` (includes 1,000-case Hypothesis metamorphic shift/scale invariance test).
- **Linters & Static Typing:** `ruff check python reference scripts tests` = **0 errors**; `mypy --strict --explicit-package-bases --ignore-missing-imports ...` = **0 errors** across 9 source files.
- **Mutation Audit (`python scripts/mutation_audit.py`):** **10/10 mutants KILLED (`kill_rate = 1.0`, `survived = 0`)** in `results/mutation_audit.json`.
- **Live Citation Audit (`python scripts/check_citations.py --live`):** **15/15 citations HTTP 200 verified, 0 retracted** in `results/citation-audit.json`.

### 6. Manuscript, Figures, Blueprint, Site, Manifest & Timestamps
- **Figures (`python scripts/generate_figures.py`):** Generated 5 Okabe–Ito vector PDF figures + 1280×640 social preview; all 14 manuscript pages visually inspected as rendered PNGs.
- **Tectonic AMS-LaTeX (`cd paper && tectonic -X compile main.tex --print`):** **14 pages, 0 errors, 0 Overfull `\hbox`, 0 warnings**; frozen to `dist/Donahue_2026_spectral_eclipse_frontier.pdf`.
- **arXiv Package (`python scripts/package_arxiv.py`):** Clean-room unpacked & compile-verified `dist/arxiv_submission.tar.gz` (8 files).
- **Axiom Sync (`python scripts/check_readme_axioms.py --require-exhaustive`):** **PASS** (49 declarations + 568 exhaustive audit + 29 README verbatim matches).
- **Blueprint & Pages (`python scripts/build_blueprint.py && python scripts/build_site.py`):** **PASS** (`build/site/`).
- **SHA-256 Manifest & Dual Timestamps (`generate_manifest.py` + `stamp_timestamps.py`):** Verified LF-only manifest cryptographically bound by DigiCert RFC 3161 `.tsr` and multi-calendar Bitcoin OpenTimestamps `.ots`.

## Hosted GitHub Actions CI Runs
- Hosted 3-OS CI (`ubuntu-latest`, `windows-latest`, `macos-latest`), Ubuntu 24.04 6-checker `lake comparator --paranoid`, GitHub Pages deployment, and Release `v1.0.0` SLSA provenance runs are recorded on GitHub Actions upon publication and archived in `0thernes-research-archive`.
