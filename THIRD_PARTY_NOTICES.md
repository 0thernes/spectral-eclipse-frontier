# Third-Party Notices and Attribution

All third-party libraries, vendored toolkits, and upstream formalization dependencies used in `spectral-eclipse-frontier` are listed below with their licenses and provenance. No third-party copyrighted manuscripts or arXiv source archives are redistributed in this repository.

## 1. Vendored Tsotchke Quantum & Geometry Toolkits (`third_party/`)

| Component | Upstream Repository | License | Usage in This Repository |
|---|---|---|---|
| **Moonlab** (`third_party/moonlab/`) | `tsotchke/moonlab` | MIT | Full $2^N$-dimensional multi-qubit XY spin-chain Hamiltonian statevector verification (`engines/moonlab/moonlab_xy_sim.cjs`) confirming exact agreement between single-excitation Jacobi dynamics $e^{-iJt}\mathbf{e}_0$ and the full $2^5=32$ Hilbert space of the staggered-field 5-qubit chain $J_{1,4}$. |
| **QGTL** (`third_party/qgtl/`) | `tsotchke/qgtl` | Apache-2.0 / MIT | Quantum Geometric Tensor & Fubini-Study metric computation (`engines/qgtl_qrng/`) verifying $g_{tt}(\mathbf{e}_0) = b_0^2$ and the Mandelstam-Tamm Early State Exclusion speed limit $\tau_{\mathrm{ESE}} \ge \pi / (2 b_0)$. |
| **Quantum-RNG (QRNG)** (`third_party/quantum_rng/`) | `tsotchke/quantum_rng` | MIT | Seeded deterministic quantum-inspired entropy stream (`engines/qgtl_qrng/`) driving the pre-registered 30-seed diagonal-disorder robustness Monte Carlo study (Build Standard B28-B32). |

See individual `LICENSE` and `PROVENANCE.md` files inside `third_party/moonlab/`, `third_party/qgtl/`, and `third_party/quantum_rng/` for exact commit SHAs and copyright headers.

## 2. Formal Verification & Compiler Toolchains

| Component | Version / Pin | License | Role |
|---|---|---|---|
| **Lean 4** | `v4.35.0` (`lean/lean-toolchain`) | Apache-2.0 | Primary theorem prover and C++ kernel. |
| **Mathlib4** | `v4.35.0` (`lean/lake-manifest.json`) | Apache-2.0 | Real/complex analysis, linear algebra, trigonometry, filters, and tactics. |
| **Batteries / Aesop / Qq** | Pinned in `lean/lake-manifest.json` | Apache-2.0 | Linter (`batteries/runLinter`) and Lean meta utilities. |
| **6-Kernel Comparators** (`leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) | Lean 4.35.0 `lake comparator --paranoid` | Apache-2.0 / MIT | Independent kernel replay of isolated `Challenge.lean` / `Solution.lean`. |
| **Eshkol** | `v1.3.6-evolve` (`tsotchke/eshkol`) | MIT | Forward-mode dual-number automatic differentiation oracle (`engines/eshkol/ese_ad_oracle.esk`) verifying exact derivatives $\mathcal{A}'(t), \mathcal{A}''(t)$ and slope certificates $G_u'(y) < 0$. |
| **Zig** | `0.17.0` | MIT | Arbitrary-precision rational (`std.math.big.int`) Hochstadt inverse spectral reconstructor (`engines/zig/`). |
| **Rust** | `1.94.1` (`#![forbid(unsafe_code)]`) | MIT / Apache-2.0 | Parallel multi-core spectral phase-diagram scanner (`engines/rust/`). |
| **GCC / G++ (ISO C11 / C++20)** | MinGW-W64 GCC 16.1.0 / Linux GCC | GPL-3.0 with GCC Runtime Library Exception | Core Hochstadt/Sturm verifier (`engines/c/`) and direct complex matrix-exponential propagator (`engines/cpp/`). |
| **NASM** | `2.16.03` | BSD-2-Clause | x86-64 AVX2+FMA tridiagonal Jacobi SpMV and Chebyshev recurrence kernel (`engines/asm/jacobi_avx2.asm`). |
| **Tectonic** | `0.17.0` | MIT | Reproducible AMS-LaTeX PDF typesetting. |
| **Python Scientific Stack** (`numpy`, `scipy`, `mpmath`, `sympy`, `matplotlib`, `pytest`, `hypothesis`, `jsonschema`, `ruff`, `mypy`) | Pinned in `requirements.txt` | BSD / MIT / PSF | Exact integer Sturm oracle, 80-digit verification, publication figures, and full test ladder. |

## 3. Build Standard Template

The repository checklist schema (`repo-standard.schema.json`), `docs/build-standard.md`, `scripts/audit-checks.tsv`, and `.github/labels.tsv` follow the Build Standard for LLMs v1.2.0.
