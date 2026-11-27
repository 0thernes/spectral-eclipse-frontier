# Complete Repository Audit Index & Table of Contents (`v1.1.0`)

Programmatic file-by-file, folder-by-folder index and table of contents of **every repository file** audited across the 3-cycle deep hardening pass for `spectral-eclipse-frontier` (`v1.1.0`) against Build Standard v1.2.0 and Defensible Independent AI Research Playbook v1.3.

- **Total Indexed Files:** **167** (plus this index `HARDENING_INDEX.md`)
- **Audit Companion Logs:** [`HARDENING_LOG.md`](HARDENING_LOG.md) · [`docs/reviews/ten-pass-audit.md`](docs/reviews/ten-pass-audit.md) · [`docs/reviews/cycle1-v1.1.md`](docs/reviews/cycle1-v1.1.md) · [`docs/reviews/cycle2-v1.1.md`](docs/reviews/cycle2-v1.1.md) · [`docs/reviews/cycle3-v1.1.md`](docs/reviews/cycle3-v1.1.md)

## Table of Contents

- [01. Root Manifests, Governance & Core Documentation](#01-root-manifests-governance-core-documentation) (36 files)
- [02. GitHub Workflows, Issue Templates & Labels](#02-github-workflows-issue-templates-labels) (10 files)
- [03. Lean 4.35.0 Formal Proof Library & Palomar Comparator](#03-lean-4350-formal-proof-library-palomar-comparator) (19 files)
- [04. Polyglot & Quantum Verification Engines (8 Toolchains)](#04-polyglot-quantum-verification-engines-8-toolchains) (19 files)
- [05. Python Public Package (spectral_eclipse)](#05-python-public-package-spectral_eclipse) (2 files)
- [06. Independent Exact Rational & 80-Digit Oracle](#06-independent-exact-rational-80-digit-oracle) (1 files)
- [07. Build, Verification, Mutation, Citation & Release Scripts](#07-build-verification-mutation-citation-release-scripts) (15 files)
- [08. Automated Test Suite (Pytest + Hypothesis + Integrity)](#08-automated-test-suite-pytest-+-hypothesis-+-integrity) (2 files)
- [09. AMS-LaTeX White Paper, Bibliography & Vector Figures](#09-ams-latex-white-paper-bibliography-vector-figures) (8 files)
- [10. Frozen Publication Artifacts (PDF & arXiv Tarball)](#10-frozen-publication-artifacts-pdf-arxiv-tarball) (2 files)
- [11. Interactive Web Observatory & Lean Blueprint](#11-interactive-web-observatory-lean-blueprint) (4 files)
- [12. Technical Documentation, ADRs & Hardening Reviews](#12-technical-documentation-adrs-hardening-reviews) (26 files)
- [13. Verified Experimental Results, Logs & Cryptographic Provenance](#13-verified-experimental-results-logs-cryptographic-provenance) (9 files)
- [14. Vendored Third-Party Quantum Libraries (Offline Provenance)](#14-vendored-third-party-quantum-libraries-offline-provenance) (14 files)

## 01. Root Manifests, Governance & Core Documentation

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`.editorconfig`](.editorconfig) | 18 lines | Cycles 2–3 | **AUDITED** |
| [`.gitattributes`](.gitattributes) | 34 lines | Cycles 2–3 | **AUDITED** |
| [`.gitignore`](.gitignore) | 44 lines | Cycles 2–3 | **AUDITED** |
| [`.gitleaks.toml`](.gitleaks.toml) | 14 lines | Cycles 2–3 | **AUDITED** |
| [`AGENTS.md`](AGENTS.md) | 70 lines | Cycles 2–3 | **AUDITED** |
| [`CHANGELOG.md`](CHANGELOG.md) | 36 lines | Cycles 2–3 | **AUDITED** |
| [`CITATION.cff`](CITATION.cff) | 28 lines | Cycles 2–3 | **AUDITED** |
| [`CLAIMS.md`](CLAIMS.md) | 33 lines | Cycles 2–3 | **AUDITED** |
| [`CLAUDE.md`](CLAUDE.md) | 1 lines | Cycles 2–3 | **AUDITED** |
| [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) | 25 lines | Cycles 2–3 | **AUDITED** |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | 18 lines | Cycles 2–3 | **AUDITED** |
| [`DEVIATIONS.md`](DEVIATIONS.md) | 27 lines | Cycles 2–3 | **AUDITED** |
| [`ERRATA.md`](ERRATA.md) | 29 lines | Cycles 2–3 | **AUDITED** |
| [`GEMINI.md`](GEMINI.md) | 1 lines | Cycles 2–3 | **AUDITED** |
| [`HARDENING_LOG.md`](HARDENING_LOG.md) | 55 lines | Cycles 2–3 | **AUDITED** |
| [`LICENSE`](LICENSE) | 190 lines | Cycles 2–3 | **AUDITED** |
| [`LICENSE-DOCS`](LICENSE-DOCS) | 34 lines | Cycles 2–3 | **AUDITED** |
| [`LIMITATIONS.md`](LIMITATIONS.md) | 26 lines | Cycles 2–3 | **AUDITED** |
| [`NOTICE`](NOTICE) | 15 lines | Cycles 2–3 | **AUDITED** |
| [`PREREGISTRATION.md`](PREREGISTRATION.md) | 44 lines | Cycles 2–3 | **AUDITED** |
| [`README.md`](README.md) | 176 lines | Cycles 2–3 | **AUDITED** |
| [`REPLICATION.md`](REPLICATION.md) | 95 lines | Cycles 2–3 | **AUDITED** |
| [`ROADMAP.md`](ROADMAP.md) | 30 lines | Cycles 2–3 | **AUDITED** |
| [`SECURITY.md`](SECURITY.md) | 18 lines | Cycles 2–3 | **AUDITED** |
| [`SUPPORT.md`](SUPPORT.md) | 8 lines | Cycles 2–3 | **AUDITED** |
| [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) | 33 lines | Cycles 2–3 | **AUDITED** |
| [`UPGRADING.md`](UPGRADING.md) | 28 lines | Cycles 2–3 | **AUDITED** |
| [`VERSION`](VERSION) | 1 lines | Cycles 2–3 | **AUDITED** |
| [`formalization.yaml`](formalization.yaml) | 58 lines | Cycles 2–3 | **AUDITED** |
| [`justfile`](justfile) | 47 lines | Cycles 2–3 | **AUDITED** |
| [`llms-full.txt`](llms-full.txt) | 20 lines | Cycles 2–3 | **AUDITED** |
| [`llms.txt`](llms.txt) | 29 lines | Cycles 2–3 | **AUDITED** |
| [`pyproject.toml`](pyproject.toml) | 42 lines | Cycles 2–3 | **AUDITED** |
| [`repo-standard.schema.json`](repo-standard.schema.json) | 245 lines | Cycles 2–3 | **AUDITED** |
| [`repo.yaml`](repo.yaml) | 117 lines | Cycles 2–3 | **AUDITED** |
| [`requirements.txt`](requirements.txt) | 15 lines | Cycles 2–3 | **AUDITED** |

## 02. GitHub Workflows, Issue Templates & Labels

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`.cursor/rules/build-standard.mdc`](.cursor/rules/build-standard.mdc) | 8 lines | Cycles 1–3 | **AUDITED** |
| [`.github/ISSUE_TEMPLATE/bug.yml`](.github/ISSUE_TEMPLATE/bug.yml) | 52 lines | Cycles 1–3 | **AUDITED** |
| [`.github/ISSUE_TEMPLATE/config.yml`](.github/ISSUE_TEMPLATE/config.yml) | 8 lines | Cycles 1–3 | **AUDITED** |
| [`.github/ISSUE_TEMPLATE/feature.yml`](.github/ISSUE_TEMPLATE/feature.yml) | 25 lines | Cycles 1–3 | **AUDITED** |
| [`.github/ISSUE_TEMPLATE/question.yml`](.github/ISSUE_TEMPLATE/question.yml) | 17 lines | Cycles 1–3 | **AUDITED** |
| [`.github/labels.tsv`](.github/labels.tsv) | 17 lines | Cycles 1–3 | **AUDITED** |
| [`.github/workflows/ci.yml`](.github/workflows/ci.yml) | 129 lines | Cycles 1–3 | **AUDITED** |
| [`.github/workflows/lean-verify.yml`](.github/workflows/lean-verify.yml) | 150 lines | Cycles 1–3 | **AUDITED** |
| [`.github/workflows/pages.yml`](.github/workflows/pages.yml) | 43 lines | Cycles 1–3 | **AUDITED** |
| [`.github/workflows/release.yml`](.github/workflows/release.yml) | 48 lines | Cycles 1–3 | **AUDITED** |

## 03. Lean 4.35.0 Formal Proof Library & Palomar Comparator

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`lean/Challenge.lean`](lean/Challenge.lean) | 290 lines | Cycle 1 | **AUDITED** |
| [`lean/Solution.lean`](lean/Solution.lean) | 276 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse.lean`](lean/SpectralEclipse.lean) | 20 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/AdversarialTests.lean`](lean/SpectralEclipse/AdversarialTests.lean) | 86 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/Chains456.lean`](lean/SpectralEclipse/Chains456.lean) | 511 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/Conjecture41.lean`](lean/SpectralEclipse/Conjecture41.lean) | 679 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/Critical9x9.lean`](lean/SpectralEclipse/Critical9x9.lean) | 2,219 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/Critical9x9Certs.lean`](lean/SpectralEclipse/Critical9x9Certs.lean) | 1,830 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/Defs.lean`](lean/SpectralEclipse/Defs.lean) | 402 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/NonSymmetricFamily.lean`](lean/SpectralEclipse/NonSymmetricFamily.lean) | 372 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/NonVacuity.lean`](lean/SpectralEclipse/NonVacuity.lean) | 220 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/RuptureAndPhase.lean`](lean/SpectralEclipse/RuptureAndPhase.lean) | 670 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/SpeedLimitAndDuality.lean`](lean/SpectralEclipse/SpeedLimitAndDuality.lean) | 503 lines | Cycle 1 | **AUDITED** |
| [`lean/SpectralEclipse/TrigBounds.lean`](lean/SpectralEclipse/TrigBounds.lean) | 1,142 lines | Cycle 1 | **AUDITED** |
| [`lean/VerifyAxioms.lean`](lean/VerifyAxioms.lean) | 119 lines | Cycle 1 | **AUDITED** |
| [`lean/comparator.json`](lean/comparator.json) | 23 lines | Cycle 1 | **AUDITED** |
| [`lean/lake-manifest.json`](lean/lake-manifest.json) | 96 lines | Cycle 1 | **AUDITED** |
| [`lean/lakefile.toml`](lean/lakefile.toml) | 27 lines | Cycle 1 | **AUDITED** |
| [`lean/lean-toolchain`](lean/lean-toolchain) | 1 lines | Cycle 1 | **AUDITED** |

## 04. Polyglot & Quantum Verification Engines (8 Toolchains)

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`engines/asm/jacobi_avx2.asm`](engines/asm/jacobi_avx2.asm) | 202 lines | Cycle 2 | **AUDITED** |
| [`engines/c/Makefile`](engines/c/Makefile) | 64 lines | Cycle 2 | **AUDITED** |
| [`engines/c/cbmc_harness.c`](engines/c/cbmc_harness.c) | 54 lines | Cycle 2 | **AUDITED** |
| [`engines/c/fuzz_hochstadt.c`](engines/c/fuzz_hochstadt.c) | 81 lines | Cycle 2 | **AUDITED** |
| [`engines/c/se_core.c`](engines/c/se_core.c) | 340 lines | Cycle 2 | **AUDITED** |
| [`engines/c/se_core.h`](engines/c/se_core.h) | 76 lines | Cycle 2 | **AUDITED** |
| [`engines/c/test_c_core.c`](engines/c/test_c_core.c) | 197 lines | Cycle 2 | **AUDITED** |
| [`engines/cpp/Makefile`](engines/cpp/Makefile) | 22 lines | Cycle 2 | **AUDITED** |
| [`engines/cpp/se_propagator.cpp`](engines/cpp/se_propagator.cpp) | 301 lines | Cycle 2 | **AUDITED** |
| [`engines/eshkol/ese_ad_oracle.esk`](engines/eshkol/ese_ad_oracle.esk) | 95 lines | Cycle 2 | **AUDITED** |
| [`engines/eshkol/run_eshkol.py`](engines/eshkol/run_eshkol.py) | 159 lines | Cycle 2 | **AUDITED** |
| [`engines/moonlab/moonlab_xy_sim.cjs`](engines/moonlab/moonlab_xy_sim.cjs) | 149 lines | Cycle 2 | **AUDITED** |
| [`engines/qgtl_qrng/Makefile`](engines/qgtl_qrng/Makefile) | 26 lines | Cycle 2 | **AUDITED** |
| [`engines/qgtl_qrng/se_qgtl_qrng.c`](engines/qgtl_qrng/se_qgtl_qrng.c) | 401 lines | Cycle 2 | **AUDITED** |
| [`engines/rust/Cargo.lock`](engines/rust/Cargo.lock) | 7 lines | Cycle 2 | **AUDITED** |
| [`engines/rust/Cargo.toml`](engines/rust/Cargo.toml) | 12 lines | Cycle 2 | **AUDITED** |
| [`engines/rust/src/main.rs`](engines/rust/src/main.rs) | 289 lines | Cycle 2 | **AUDITED** |
| [`engines/zig/build.zig`](engines/zig/build.zig) | 21 lines | Cycle 2 | **AUDITED** |
| [`engines/zig/src/main.zig`](engines/zig/src/main.zig) | 333 lines | Cycle 2 | **AUDITED** |

## 05. Python Public Package (spectral_eclipse)

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`python/spectral_eclipse/__init__.py`](python/spectral_eclipse/__init__.py) | 26 lines | Cycle 2 | **AUDITED** |
| [`python/spectral_eclipse/core.py`](python/spectral_eclipse/core.py) | 129 lines | Cycle 2 | **AUDITED** |

## 06. Independent Exact Rational & 80-Digit Oracle

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`reference/exact_oracle.py`](reference/exact_oracle.py) | 202 lines | Cycle 2 | **AUDITED** |

## 07. Build, Verification, Mutation, Citation & Release Scripts

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`scripts/analyze_qrng_study.py`](scripts/analyze_qrng_study.py) | 164 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/audit-checks.tsv`](scripts/audit-checks.tsv) | 107 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/audit-repo.sh`](scripts/audit-repo.sh) | 202 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/build_blueprint.py`](scripts/build_blueprint.py) | 140 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/build_site.py`](scripts/build_site.py) | 40 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/check_citations.py`](scripts/check_citations.py) | 201 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/check_readme_axioms.py`](scripts/check_readme_axioms.py) | 125 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/generate_figures.py`](scripts/generate_figures.py) | 423 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/generate_llms_full.py`](scripts/generate_llms_full.py) | 51 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/generate_manifest.py`](scripts/generate_manifest.py) | 135 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/mutation_audit.py`](scripts/mutation_audit.py) | 179 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/package_arxiv.py`](scripts/package_arxiv.py) | 98 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/run_polyglot_parity.py`](scripts/run_polyglot_parity.py) | 153 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/stamp_timestamps.py`](scripts/stamp_timestamps.py) | 177 lines | Cycles 1–3 | **AUDITED** |
| [`scripts/test_lean_negative.py`](scripts/test_lean_negative.py) | 65 lines | Cycles 1–3 | **AUDITED** |

## 08. Automated Test Suite (Pytest + Hypothesis + Integrity)

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`examples/quickstart.py`](examples/quickstart.py) | 51 lines | Cycle 2 | **AUDITED** |
| [`tests/test_all.py`](tests/test_all.py) | 366 lines | Cycle 2 | **AUDITED** |

## 09. AMS-LaTeX White Paper, Bibliography & Vector Figures

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`paper/figures/fig1_phase_diagram.pdf`](paper/figures/fig1_phase_diagram.pdf) | 32,542 B (binary) | Cycle 3 | **AUDITED** |
| [`paper/figures/fig2_conj41_mechanism.pdf`](paper/figures/fig2_conj41_mechanism.pdf) | 36,057 B (binary) | Cycle 3 | **AUDITED** |
| [`paper/figures/fig3_universal_3r2.pdf`](paper/figures/fig3_universal_3r2.pdf) | 38,133 B (binary) | Cycle 3 | **AUDITED** |
| [`paper/figures/fig4_nonsym_j14_spiral.pdf`](paper/figures/fig4_nonsym_j14_spiral.pdf) | 42,135 B (binary) | Cycle 3 | **AUDITED** |
| [`paper/figures/fig5_qgtl_qrng_disorder.pdf`](paper/figures/fig5_qgtl_qrng_disorder.pdf) | 32,528 B (binary) | Cycle 3 | **AUDITED** |
| [`paper/main.pdf`](paper/main.pdf) | 380,460 B (binary) | Cycle 3 | **AUDITED** |
| [`paper/main.tex`](paper/main.tex) | 557 lines | Cycle 3 | **AUDITED** |
| [`paper/refs.bib`](paper/refs.bib) | 180 lines | Cycle 3 | **AUDITED** |

## 10. Frozen Publication Artifacts (PDF & arXiv Tarball)

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`dist/Donahue_2026_spectral_eclipse_frontier.pdf`](dist/Donahue_2026_spectral_eclipse_frontier.pdf) | 380,460 B (binary) | Cycle 3 | **AUDITED** |
| [`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz) | 184,303 B (binary) | Cycle 3 | **AUDITED** |

## 11. Interactive Web Observatory & Lean Blueprint

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`web/blueprint/blueprint.json`](web/blueprint/blueprint.json) | 150 lines | Cycle 3 | **AUDITED** |
| [`web/blueprint/index.html`](web/blueprint/index.html) | 134 lines | Cycle 3 | **AUDITED** |
| [`web/index.html`](web/index.html) | 110 lines | Cycle 3 | **AUDITED** |
| [`web/observatory.js`](web/observatory.js) | 101 lines | Cycle 3 | **AUDITED** |

## 12. Technical Documentation, ADRs & Hardening Reviews

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`docs/MEGA_ATLAS_CROSSCHECK.md`](docs/MEGA_ATLAS_CROSSCHECK.md) | 26 lines | Cycles 1–3 | **AUDITED** |
| [`docs/adr/0001-divided-difference-bernstein-architecture.md`](docs/adr/0001-divided-difference-bernstein-architecture.md) | 20 lines | Cycles 1–3 | **AUDITED** |
| [`docs/adr/0002-dual-licensing-and-six-kernel-palomar.md`](docs/adr/0002-dual-licensing-and-six-kernel-palomar.md) | 20 lines | Cycles 1–3 | **AUDITED** |
| [`docs/adr/0003-polyglot-parity-and-b20-cancellation-guard.md`](docs/adr/0003-polyglot-parity-and-b20-cancellation-guard.md) | 20 lines | Cycles 1–3 | **AUDITED** |
| [`docs/adr/0004-preregistered-qrng-codimension-study.md`](docs/adr/0004-preregistered-qrng-codimension-study.md) | 19 lines | Cycles 1–3 | **AUDITED** |
| [`docs/architecture.md`](docs/architecture.md) | 39 lines | Cycles 1–3 | **AUDITED** |
| [`docs/benchmarks.md`](docs/benchmarks.md) | 28 lines | Cycles 1–3 | **AUDITED** |
| [`docs/build-standard.md`](docs/build-standard.md) | 1,742 lines | Cycles 1–3 | **AUDITED** |
| [`docs/configuration.md`](docs/configuration.md) | 20 lines | Cycles 1–3 | **AUDITED** |
| [`docs/faq.md`](docs/faq.md) | 18 lines | Cycles 1–3 | **AUDITED** |
| [`docs/glossary.md`](docs/glossary.md) | 12 lines | Cycles 1–3 | **AUDITED** |
| [`docs/index.md`](docs/index.md) | 36 lines | Cycles 1–3 | **AUDITED** |
| [`docs/literature-search.md`](docs/literature-search.md) | 11 lines | Cycles 1–3 | **AUDITED** |
| [`docs/media/social-preview.png`](docs/media/social-preview.png) | 126,981 B (binary) | Cycles 1–3 | **AUDITED** |
| [`docs/operations.md`](docs/operations.md) | 28 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/cycle1-v1.1.md`](docs/reviews/cycle1-v1.1.md) | 15 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/cycle1.md`](docs/reviews/cycle1.md) | 15 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/cycle2-v1.1.md`](docs/reviews/cycle2-v1.1.md) | 20 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/cycle2.md`](docs/reviews/cycle2.md) | 16 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/cycle3-v1.1.md`](docs/reviews/cycle3-v1.1.md) | 19 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/cycle3.md`](docs/reviews/cycle3.md) | 19 lines | Cycles 1–3 | **AUDITED** |
| [`docs/reviews/ten-pass-audit.md`](docs/reviews/ten-pass-audit.md) | 16 lines | Cycles 1–3 | **AUDITED** |
| [`docs/run-log.md`](docs/run-log.md) | 50 lines | Cycles 1–3 | **AUDITED** |
| [`docs/statement-fidelity.md`](docs/statement-fidelity.md) | 24 lines | Cycles 1–3 | **AUDITED** |
| [`docs/threat-model.md`](docs/threat-model.md) | 24 lines | Cycles 1–3 | **AUDITED** |
| [`docs/verification.md`](docs/verification.md) | 35 lines | Cycles 1–3 | **AUDITED** |

## 13. Verified Experimental Results, Logs & Cryptographic Provenance

| File | Size / Lines | Hardening Cycle | Status |
| :--- | ---: | :--- | :---: |
| [`data/MANIFEST.sha256`](data/MANIFEST.sha256) | 40 lines | Cycles 1–3 | **AUDITED** |
| [`data/MANIFEST.sha256.ots`](data/MANIFEST.sha256.ots) | 861 B (binary) | Cycles 1–3 | **AUDITED** |
| [`data/MANIFEST.sha256.tsr`](data/MANIFEST.sha256.tsr) | 6,007 B (binary) | Cycles 1–3 | **AUDITED** |
| [`results/citation-audit.json`](results/citation-audit.json) | 279 lines | Cycles 1–3 | **AUDITED** |
| [`results/lean-axioms-all.log`](results/lean-axioms-all.log) | 83 lines | Cycles 1–3 | **AUDITED** |
| [`results/mutation_audit.json`](results/mutation_audit.json) | 68 lines | Cycles 1–3 | **AUDITED** |
| [`results/polyglot_parity.json`](results/polyglot_parity.json) | 40 lines | Cycles 1–3 | **AUDITED** |
| [`results/qgtl_qrng_analysis.json`](results/qgtl_qrng_analysis.json) | 482 lines | Cycles 1–3 | **AUDITED** |
| [`results/qgtl_qrng_study.json`](results/qgtl_qrng_study.json) | 62 lines | Cycles 1–3 | **AUDITED** |

## 14. Vendored Third-Party Quantum Libraries (Offline Provenance)

Vendored offline-reproducible upstream quantum libraries (`14` files; licenses verified in [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) and [`NOTICE`](NOTICE); compiled & linked cleanly during Cycle 2).

| Vendored Directory | File Count | Audit Scope | Status |
| :--- | ---: | :--- | :---: |
| `third_party/moonlab/` | 4 | Upstream license, build flags, offline linkage (`Cycle 2 (Vendored Upstream)`) | **AUDITED** |
| `third_party/qgtl/` | 5 | Upstream license, build flags, offline linkage (`Cycle 2 (Vendored Upstream)`) | **AUDITED** |
| `third_party/quantum_rng/` | 5 | Upstream license, build flags, offline linkage (`Cycle 2 (Vendored Upstream)`) | **AUDITED** |

