# Benchmarks & Execution Timings

This project makes **no speed, latency, or SOTA runtime performance claims** (`repo.yaml` flag `perf: false`). The timings below are recorded strictly for reproducibility and capacity planning during clean-room verification.

## Reference Hardware & Toolchains

- **Host OS / CPU:** Windows 11 x86-64 (AVX2 + FMA enabled), ReFS Dev Drive (`Z:\`).
- **Lean / Mathlib:** `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (cached `.olean`s).
- **Compilers:** GCC/G++ (MinGW-w64 / Ubuntu GCC 13), NASM 2.16+, Rust `rustc` / `cargo` (release mode, zero `unsafe`), Zig `0.17.0` (`-OReleaseSafe`), Eshkol `v1.3.6`, Node.js v20+, Python 3.9–3.12, Tectonic 0.15+.

## Measured Verification Wall-Clock Durations

| Stage | Command | Observed Duration | Notes |
| :--- | :--- | :---: | :--- |
| Lean full build (cached Mathlib) | `cd lean && lake build SpectralEclipse Challenge Solution VerifyAxioms` | ~140 s | `Critical9x9Certs.lean` (~60 s) + `Critical9x9.lean` (~41 s) + `VerifyAxioms.lean` (~36 s) |
| Lean axiom audit (572 theorems) | `cd lean && lake env lean VerifyAxioms.lean` | ~18 s | Audits all 49 explicit `#print axioms` + 572 `Lean.collectAxioms` constants |
| Lean negative tests (3 cases) | `python scripts/test_lean_negative.py` | ~15 s | Confirms kernel rejection of mutated thresholds |
| Python pytest ladder (15 tests) | `python -m pytest -v tests/` | 2.9–3.1 s | Includes 1,000-case Hypothesis metamorphic suite |
| B13 mutation audit (10 mutants) | `python scripts/mutation_audit.py` | ~42 s | Isolated sandbox copy; 10/10 mutants killed (100.0%) |
| C11 + NASM AVX2 (`10^5` fuzz) | `engines/c/test_c_core` | <0.2 s | Hardware AVX2+FMA active; max error $1.78\times 10^{-15}$ |
| C++20 direct matrix exp (16 chains) | `engines/cpp/se_propagator` | <0.2 s | Exact QL eigendecomposition + cancellation guard |
| Safe Rust scan ($R=2..5$ + 965 QSL) | `cargo run --release` | <0.4 s | Multi-core Rayon scan, zero `unsafe` |
| Zig 0.17.0 exact $\mathbb{Q}$ (10 chains) | `zig run -OReleaseSafe src/main.zig` | ~1.5 s | Arbitrary-precision `BigInt` rational Lanczos |
| Eshkol v1.3.6 native AD | `python engines/eshkol/run_eshkol.py` | ~1.2 s | Native forward-mode AD vs dual-number parity ($1.33\times 10^{-15}$) |
| Moonlab WASM 32-dim Trotter | `node engines/moonlab/moonlab_xy_sim.cjs` | ~0.6 s | 5-qubit 2nd-order Strang-Trotter on `moonlab.wasm` |
| QGTL + QRNG 4-arm study (30 seeds) | `engines/qgtl_qrng/se_qgtl_qrng` | ~2.1 s | 4 arms $\times$ 5 disorder levels $\times$ 30 paired seeds |
| Full 8-engine cross-parity | `python scripts/run_polyglot_parity.py` | ~4.5 s | 0 mismatches across 13 canonical chains |
| Figures + Tectonic PDF + arXiv | `python scripts/generate_figures.py && python scripts/package_arxiv.py` | ~14 s | 5 vector PDFs + 14-page 0.00pt-overfull PDF + clean-room tarball check |
