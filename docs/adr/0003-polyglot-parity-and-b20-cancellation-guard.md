# ADR-0003: Eight-Engine Polyglot Cross-Parity and the B20 Float64 Cancellation Guard

- **Status:** Accepted
- **Date:** 2026-11-26
- **Author:** Alexander Stephen Donahue

## Context

Numerical evaluation of the return amplitude $A(t) = \sum_k w_k e^{-i \lambda_k t}$ for high-order PST spin chains ($N \ge 7$) suffers from severe IEEE-754 `float64` catastrophic cancellation near the PST time $t = \pi$, where $|A(t)| = O((\pi - t)^{N-1})$ drops below machine epsilon ($\approx 10^{-16}$) even when $A(t) \neq 0$. A naive floating-point zero finder would hallucinate spurious ESE events near $t = \pi$.

## Decision

1. **Exact Ground-Truth Oracles First:** Use exact Sturm sequences over $\mathbb{Q}[u]$ (`reference/exact_oracle.py`) and arbitrary-precision rational Hochstadt reconstruction in Zig (`engines/zig/src/main.zig`) as the non-rounding ground truth for ESE existence, supplemented by 80-digit `mpmath` root polishing.
2. **Explicit B20 Float64 Cancellation Guard:** Define `FLOAT64_CANCELLATION_MARGIN` in `python/spectral_eclipse/core.py` and document the exact $(\pi - t)^{N-1}$ conditioning bound in the white paper, `LIMITATIONS.md`, and regression tests in `tests/test_all.py`.
3. **Eight-Engine Differential Cross-Parity (`B11`):** Cross-verify 13 canonical chains across 8 heterogeneous implementations — NASM x86-64 AVX2+FMA, ISO C11, ISO C++20, Safe Rust (`#![forbid(unsafe_code)]`), Zig exact $\mathbb{Q}$, Eshkol v1.3.6 native AD, Moonlab WASM 32-dim multi-qubit Trotter-Suzuki, and QGTL + Quantum-RNG — via `scripts/run_polyglot_parity.py`.

## Consequences

- **Positive:** Zero mismatches across all 8 engines (`results/polyglot_parity.json`), full physical verification of the single-excitation subspace inside the $2^5 = 32$-dimensional multi-qubit XY Hilbert space (`Moonlab`), and permanent protection against float64 cancellation illusions.
- **Trade-off:** Multi-toolchain builds increase repository surface area, mitigated by clean Makefiles, offline vendoring, and fallback/CI separation.
