# Execution & Verification Run Log (`B40`)

Chronological log of verified local and CI execution runs for `spectral-eclipse-frontier` (`v1.0.0` baseline and `v1.1.0` deep-hardened release), recorded directly from live tool outputs (never fabricated or backfilled).

---

## Release `v1.1.0` Deep-Hardening Verification Runs (2026-11-27)

### 1. Lean 4.35.0 Full Library, Palomar Isolation, Zero-Error Linter & 572-Theorem Axiom Audit
- **Commands:**
  ```bash
  cd lean && lake build SpectralEclipse Challenge Solution VerifyAxioms
  lake env lean VerifyAxioms.lean
  lake exe runLinter SpectralEclipse Solution
  ```
- **Live Output (`results/lean-axioms-all.log`):**
  - **0 errors, 0 warnings, 0 `sorry`, 0 `admit`, 0 custom `axiom`, 0 `native_decide`**.
  - **52 explicit `#print axioms` declarations** (17 primary theorems + 18 `NonVacuity` witnesses + 5 `AdversarialTests` refutations + 12 `ComparatorTarget` bridges) strictly within `[propext, Classical.choice, Quot.sound]`.
  - **Exhaustive `Lean.collectAxioms` sentinel:** `ALL_THEOREMS_AXIOM_AUDIT_PASS: checked 572 theorems across SpectralEclipse — 0 disallowed axioms.`
  - **Batteries Linter (`runLinter`):** `-- Linting passed for SpectralEclipse.` (0 `docBlame` or lint errors after documenting `hochstadtWeightOdd`; promoted to a hard CI gate in `.github/workflows/lean-verify.yml`).
  - **Live `sorry`-Tamper Comparator CI Gate:** Added to `.github/workflows/lean-verify.yml` (temporarily injects `sorry` into `Solution.lean` via `trap` restore and asserts `lake comparator` exits nonzero).
- **Negative Kernel Elaboration Gate (`python scripts/test_lean_negative.py`):** **3/3 PASSED** (`mutated_11x11_threshold_m5`, `mutated_4x4_false_p3`, `mutated_J14_wrong_variance` all rejected by Lean 4.35.0).

### 2. C11 / NASM AVX2+FMA & QGTL/QRNG Study Re-Run After Deviation #1 Optimizer Fix
- **C11 + NASM AVX2+FMA (`engines/c/se_core.c` with `bessel_j_array` OOM/zero-norm propagation):**
  - `[C/ASM] ALL TESTS PASSED (0 errors)` (`max|SpMV| = 8.882e-16`, `max|Cheb| = 1.776e-15`, `100,000`-iter Hochstadt fuzz `1.688e-14`).
- **Pre-Registered 4-Arm QRNG Disorder Study (`engines/qgtl_qrng/se_qgtl_qrng` after Deviation #1 multi-bracket refinement fix, see [`DEVIATIONS.md`](../DEVIATIONS.md)):**
  - **Commands:** `engines/qgtl_qrng/se_qgtl_qrng.exe results/qgtl_qrng_study.json` followed by `python scripts/analyze_qrng_study.py`
  - **Clean-Limit Verification ($\varepsilon = 0$):** All 4 treatment arms now return exact `0.000000e+00` (fixing the `v1.0.0` single-bracket trapping on $J_{1,4}$).
  - **Primary Endpoint ($\varepsilon = 0.05$, $K = 30$ paired seeds, `results/qgtl_qrng_analysis.json`):**
    - **H1** ($7\times 7$ Conjecture 4.1 ESE vs. no-ESE, $\varepsilon = 0.05$): `treat_med = 0.00233`, `ctrl_med = 0.01539`, `mean_diff = +0.01525` (`95% CI [+0.00945, +0.02125]`), Cohen's $d_z = +0.91$, Cliff's $\delta = +0.542$, $p_{\mathrm{Holm}} = 0.0004$ ($\beta = 0.90$) -> **SIGNIFICANT**.
    - **H2** ($8\times 8$ even rupture $m=1$ vs. $6\times 6$ no-ESE, $\varepsilon = 0.05$): `treat_med = 0.00347`, `ctrl_med = 0.10373`, `mean_diff = +0.10110` (`95% CI [+0.09878, +0.10363]`), $d_z = +14.68$, $\delta = +1.000$, $p_{\mathrm{Holm}} = 0.0004$ ($\beta = 1.14$) -> **SIGNIFICANT**.
    - **H3** ($11\times 11$ supercritical $m=6$ vs. subcritical $m=5$, $\varepsilon = 0.05$): `treat_med = 0.00685`, `ctrl_med = 0.00995`, `mean_diff = +0.00321` (`95% CI [+0.00185, +0.00459]`), $d_z = +0.83$, $\delta = +0.247$, $p_{\mathrm{Holm}} = 0.0004$ ($\beta = 1.49$) -> **SIGNIFICANT**.
    - **H4** ($5\times 5$ staggered complex $J_{1,4}$ vs. $5\times 5$ Krawtchouk no-ESE, $\varepsilon = 0.05$): `treat_med = 0.01626`, `ctrl_med = 0.01377`, `mean_diff = +0.00007` (`95% CI [-0.00619, +0.00689]`), $d_z = +0.00$, $\delta = -0.078$, $p_{\mathrm{Holm}} = 0.9855$ ($\beta = 0.83$) -> **PRE-REGISTERED NULL** (honestly reported; codimension-2 complex zero lifting vs. codimension-1 real crossing protection).

### 3. Polyglot Parity, Python QA, Mutation Audit, Live Retraction-Checked Citations & Publication Pipeline
- **8-Engine Parity (`python scripts/run_polyglot_parity.py`):** `"all_passed": true`, `"mismatches": []` across all 13 canonical spin-chain test cases.
- **Pytest + Hypothesis (`python -m pytest -v tests/`):** **22/22 PASSED** (including 1,000-case Hypothesis metamorphic shift/scale invariance, single-version manifest check, `repo.yaml` JSON Schema validation, zero broken relative markdown links, zero stale identifiers, exact $\varepsilon=0$ regression, and manifest tamper rejection).
- **Linters & Static Typing:** `ruff check python reference scripts tests` = **0 errors** (including POSIX `+x` mode `100755` on all shebang scripts for Linux CI); `mypy --strict --explicit-package-bases --ignore-missing-imports python reference scripts tests` = **0 errors** across every module; `cargo clippy --all-targets -- -D warnings` = **0 warnings**.
- **Mutation Audit (`python scripts/mutation_audit.py`):** **10/10 mutants KILLED (`kill_rate = 1.0`, `survived = 0`)**.
- **Live Citation & Retraction Audit (`python scripts/check_citations.py`):** **15/15 citations HTTP 200 verified, title-overlap validated, 0 retracted** (`results/citation-audit.json`).
- **Security Dependencies:** `requirements.txt` upgraded (`pillow==13.0.0`, `pytest==9.2.0`, `pygments==2.21.0`, unused `PyMuPDF` removed) -> **0 Dependabot alerts, 0 `osv-scanner` CVEs**.
- **Manuscript, Figures, Blueprint, Site, Manifest & Timestamps:** Dynamically regenerated Figure 5 + Tectonic 0-error/0-warning/0-overfull-hbox PDF + clean-room `arxiv_submission.tar.gz` + strict-CSP GitHub Pages (`web/observatory.js`) + LF-normalized `data/MANIFEST.sha256` with DigiCert RFC 3161 `.tsr` and Bitcoin OpenTimestamps `.ots`.

---

## Historical `v1.0.0` Baseline Verification Runs (2026-11-26 / 2026-11-27)

- **Root Pre-Registration Lock (`1dac632`):** Locked `PREREGISTRATION.md` before executing any QRNG disorder experiment.
- **Baseline `v1.0.0` Tag (`8d6cf7c`):** 568 audited Lean theorems, 6-checker Palomar comparator PASS on Ubuntu 24.04 CI, 3-OS Python/native CI PASS, GitHub Pages deployed, Software Heritage snapshot `swh:1:snp:37fd5b55ad30a2e1cedc2949415bfacf4d5d1efc`, and registered as `0TH-2026-024` in `0thernes/0thernes-research-archive`. Note: `v1.0.0` had typographical errors in this run-log (transposed H2/H3 arm labels, incorrect Cliff's $\delta$ transcription, and `--study` CLI flag typo) and the `compute_interior_min` single-bracket optimizer bug; all were corrected transparently in `v1.1.0` (see [`ERRATA.md`](../ERRATA.md) and [`DEVIATIONS.md`](../DEVIATIONS.md)).
