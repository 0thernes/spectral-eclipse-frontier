# Replication Guide

This document provides exact, clean-room, step-by-step instructions to independently reproduce every Lean 4.35.0 proof, all eight polyglot and quantum engines, the pre-registered QRNG study, all five publication figures, the frozen AMS-LaTeX PDF, the standalone arXiv tarball, and cryptographic integrity checks.

## Prerequisites

- **Lean 4.35.0:** Installed via `elan` (`lean/lean-toolchain` pins `leanprover/lean4:v4.35.0`; `lean/lake-manifest.json` pins Mathlib `v4.35.0`).
- **Python 3.10–3.12:** With `pip install -r requirements.txt`.
- **Polyglot Toolchains (for full 8-engine parity):** `gcc` / `g++` (C11 & C++20), `nasm` (optional x86-64 AVX2 assembly; automatic scalar C11 fallback if absent), `rustc` / `cargo`, `zig` (0.17.0+), `node` (v18+ for Moonlab WASM), `eshkol-run` (optional; automatic Python dual-number fallback if absent).
- **LaTeX:** `tectonic` (v0.15+) for reproducible PDF and arXiv tarball compilation.
- **Timestamp verification:** `openssl` (for DigiCert RFC 3161 `.tsr` verification).

## Step 1: Machine-Checked Lean 4.35.0 Verification & 6-Checker Palomar Replay

```bash
cd lean
lake exe cache get
lake build SpectralEclipse Challenge Solution VerifyAxioms
lake env lean VerifyAxioms.lean
# On Linux with bubblewrap installed (exact CI command):
lake comparator --config comparator.json --paranoid
cd ..
python scripts/test_lean_negative.py
python scripts/check_readme_axioms.py --require-exhaustive
```

Expected sentinel:
`ALL_THEOREMS_AXIOM_AUDIT_PASS: checked 572 theorems across SpectralEclipse — 0 disallowed axioms.`

## Step 2: Python Verification Ladder & B13 Mutation Audit

```bash
python -m pip install -r requirements.txt
python -m pytest -v tests/
python reference/exact_oracle.py
python scripts/mutation_audit.py
ruff check python reference scripts tests
mypy --strict --explicit-package-bases --ignore-missing-imports python/spectral_eclipse reference/exact_oracle.py scripts/check_readme_axioms.py scripts/mutation_audit.py scripts/test_lean_negative.py scripts/analyze_qrng_study.py scripts/run_polyglot_parity.py scripts/check_citations.py
```

Expected: `15 passed` (including 1,000-case Hypothesis metamorphic suite), `10/10` mutants killed (`100.0%`), `0` ruff errors, `0` mypy errors.

## Step 3: Build & Cross-Verify All 8 Polyglot & Quantum Engines

```bash
# 1. NASM AVX2+FMA Assembly + ISO C11
make -C engines/c clean all && ./engines/c/test_c_core

# 2. ISO C++20 direct matrix-exponential propagator
make -C engines/cpp clean all && ./engines/cpp/se_propagator

# 3. Safe Rust multi-core scanner
cd engines/rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release && cd ../..

# 4. Zig 0.17.0 exact arbitrary-precision rational Hochstadt engine
cd engines/zig && zig run -OReleaseSafe src/main.zig && cd ../..

# 5. Eshkol v1.3.6 native AD (or pure-Python dual fallback)
python engines/eshkol/run_eshkol.py

# 6. Moonlab WASM 5-qubit (32-dim) many-body XY+Z simulator
node engines/moonlab/moonlab_xy_sim.cjs

# 7. Vendored QGTL + Quantum-RNG study & statistical analysis
make -C engines/qgtl_qrng clean all && ./engines/qgtl_qrng/se_qgtl_qrng
python scripts/analyze_qrng_study.py

# 8. Automated 8-engine cross-parity report (0 mismatches)
python scripts/run_polyglot_parity.py
```

## Step 4: Figures, Paper, Standalone arXiv Tarball, Web Portal & Integrity Checks

```bash
python scripts/check_citations.py
python scripts/generate_figures.py
python scripts/package_arxiv.py
python scripts/build_blueprint.py
python scripts/build_site.py
python scripts/generate_manifest.py --verify
python scripts/stamp_timestamps.py --verify
```

## Clean-Room Replication Log (`B44`)

| Date | Operator / Environment | Scope | Outcome |
|---|---|---|---|
| 2026-11-27 | Author (A. S. Donahue) — Local Windows 11 x86-64 clean-room run | Lean 4.35.0 (572 audited theorems, 0 sorry), 8/8 polyglot engines (0 mismatches), 15/15 pytest, 10/10 mutation kill, clean-room arXiv tarball | PASS (internal) |
| 2026-11-27 | Hosted GitHub Actions CI (`ubuntu-latest`, `windows-latest`, `macos-latest`, `ubuntu-24.04`) | 3-OS Python/Hypothesis/manifest/timestamp matrix + Ubuntu native C11/ASan/C++20/Rust/Moonlab/QGTL + 6-checker `lake comparator --paranoid` | PASS (hosted CI) |

- **Independent Outside Human Operator Replication (`B44`):** **OPEN** (`0` independent external human operators have filed a replication report yet; issue reports or replication confirmations are welcomed via GitHub Issues; `repo.yaml` retains `B44: partial` until an external human operator logs an independent run).
