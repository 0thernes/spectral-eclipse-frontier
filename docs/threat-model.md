# Threat Model & Verification Integrity (`B36`)

Because `spectral-eclipse-frontier` claims machine-checked mathematical proofs and reproducible quantum-mechanical computations, its primary security and integrity threats are **formal proof evasion, numerical unsoundness, supply-chain tampering, and static-portal injection**.

## 1. Threat Matrix & Concrete Mitigations

| Threat ID | Attack / Failure Vector | Impact | Implemented Mitigation |
|---|---|---|---|
| **T1** | **Proof Evasion / Custom Axioms / `sorry`** (introducing an unsound axiom, `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, or redefining a target statement weakly in `Solution.lean`) | False mathematical claims appearing to compile | (1) `lean/Challenge.lean` isolates all 12 targets using Mathlib-only imports; (2) `lake comparator --config comparator.json --paranoid` replays every proof across **6 independent Lean 4.35.0 checkers** inside `bubblewrap` (`lean`, `leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`); (3) nested-comment-aware Lean lexer scan in `lean-verify.yml`; (4) exhaustive `Lean.collectAxioms` over all 572 theorems in `VerifyAxioms.lean`; (5) live negative kernel rejection tests (`scripts/test_lean_negative.py`); (6) `autoImplicit = false` in `lean/lakefile.toml`. |
| **T2** | **Vacuous Hypotheses or Statement Drift** (proving a theorem with unsatisfiable preconditions or drifting from Escobar–Garcia–Minenkova's statement) | Formally valid proof of the wrong theorem | `lean/SpectralEclipse/NonVacuity.lean` constructs explicit concrete witnesses for every theorem; `lean/SpectralEclipse/AdversarialTests.lean` proves explicit counter-witnesses on wrong constants/thresholds; `docs/statement-fidelity.md` audits exact correspondence including unreduced arbitrary real-scaled `conjecture_4_1_unreduced`. |
| **T3** | **Floating-Point Catastrophic Cancellation (`B20`)** (IEEE-754 `float64` losing 16 digits when evaluating $A(t)$ near $t = \pi$ where $A(t) = O((\pi - t)^{N-1})$) | Spurious false-positive ESE zeros near $t = \pi$ | Discovered and mathematically characterized; guarded via `FLOAT64_CANCELLATION_MARGIN` + exact Sturm root counting on $P(u) = 0$ + Zig `std.math.big.int` exact $\mathbb{Q}$ + 80-digit `mpmath` cross-parity + dedicated regression test in `tests/test_all.py`. |
| **T4** | **Post-Hoc Data Dredging / HARKing (`B32`)** (changing QRNG seeds, disorder levels, or dropping null results after seeing output) | Inflated Type I error and survivorship bias | `PREREGISTRATION.md` locked in root commit `1dac632` before running any QRNG simulation; all 4 primary hypotheses reported including the honest H4 null ($p_{\text{Holm}} = 0.988$); Holm–Bonferroni FWER control enforced. |
| **T5** | **Dependency / Supply-Chain Tampering (`B35`)** (compromised PyPI/crates/third-party upstream or mutated release binaries) | Non-reproducible or malicious build artifacts | Pinned `requirements.txt`, `engines/rust/Cargo.lock`, `lean/lake-manifest.json`; offline-vendored `third_party/{moonlab,qgtl,quantum_rng}`; SHA-256-verified `osv-scanner` and `gitleaks` in CI; LF-normalized `data/MANIFEST.sha256` bound to DigiCert RFC 3161 `.tsr` + Bitcoin `.ots` + Sigstore SLSA attestations on GitHub Release `v1.0.0`. |
| **T6** | **Static Web Portal XSS / Mixed Content / CDN Tracking** | Client-side script injection or broken offline rendering | Zero external CDN dependencies in `web/index.html` and `web/blueprint/index.html`; strict `Content-Security-Policy` meta tag; all dynamic canvas rendering uses numeric state (no `innerHTML` with untrusted input). |
| **T7** | **Secret Leakage (`A24`)** | Exposed API keys or credentials in git history | `.gitleaks.toml` + CI `gitleaks` scan + `.env` ignored in `.gitignore`; zero external API keys required anywhere in the project. |

## 2. Out-of-Scope Threats

- Physical side-channel attacks against host CPUs executing the AVX2/C/Rust engines (no cryptographic secrets are processed).
- Hardware quantum-computer calibration errors (all quantum-mechanical computations here are exact/numerical classical simulations of finite-dimensional Hamiltonians; no physical QPU is accessed).

## 3. Responsible Disclosure

See [`SECURITY.md`](../SECURITY.md) for vulnerability and proof-soundness reporting procedures.
