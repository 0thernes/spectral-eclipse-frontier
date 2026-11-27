# Threat Model & Verification Integrity (`B36`)

Because `spectral-eclipse-frontier` claims machine-checked mathematical proofs and reproducible quantum-mechanical computations, its primary security and integrity threats are **formal proof evasion, numerical unsoundness, supply-chain tampering, and static-portal injection**.

## 1. Threat Matrix & Concrete Mitigations

| Threat ID | Attack / Failure Vector | Impact | Implemented Mitigation |
|---|---|---|---|
| **T1** | **Proof Evasion / Custom Axioms / `sorry`** (introducing an unsound axiom, `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, or redefining a target statement weakly in `Solution.lean`) | False mathematical claims appearing to compile | (1) `lean/Challenge.lean` isolates all 12 targets using Mathlib-only imports; (2) `lake comparator --config comparator.json --paranoid` replays every proof across **6 independent Lean 4.35.0 checkers** inside `bubblewrap` (`lean`, `leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`); (3) nested-comment-aware Lean lexer scan in `lean-verify.yml`; (4) exhaustive `Lean.collectAxioms` over all 571 theorems in `VerifyAxioms.lean`; (5) live negative kernel rejection tests (`scripts/test_lean_negative.py`) + live `sorry`-tamper comparator rejection gate in `lean-verify.yml`; (6) `autoImplicit = false` and zero-error Batteries `runLinter` gate. |
| **T2** | **Vacuous Hypotheses or Statement Drift** (proving a theorem with unsatisfiable preconditions or drifting from Escobar–Garcia–Minenkova's statement) | Formally valid proof of the wrong theorem | `lean/SpectralEclipse/NonVacuity.lean` constructs 18 explicit concrete witnesses covering every theorem & comparator target; `lean/SpectralEclipse/AdversarialTests.lean` proves 5 explicit counter-theorems on false conjecture variants; `docs/statement-fidelity.md` audits exact correspondence including unreduced arbitrary real-scaled `conjecture_4_1_7x7_unreduced`. |
| **T3** | **Floating-Point Catastrophic Cancellation (`B20`)** (IEEE-754 `float64` losing 16 digits when evaluating $A(t)$ near $t = \pi$ where $A(t) = O((\pi - t)^{N-1})$) | Spurious false-positive ESE zeros near $t = \pi$ | Discovered and mathematically characterized; guarded via exported `FLOAT64_CANCELLATION_MARGIN` + exact Sturm root counting on $P(u) = 0$ + Zig `std.math.big.int` exact $\mathbb{Q}$ + 80-digit `mpmath` cross-parity + dedicated regression test in `tests/test_all.py`. |
| **T4** | **Post-Hoc Data Dredging / HARKing (`B32`)** (changing QRNG seeds, disorder levels, or dropping null results after seeing output) | Inflated Type I error and survivorship bias | `PREREGISTRATION.md` locked in root commit `1dac632` before running any QRNG simulation; any numerical bug fix recorded append-only in `DEVIATIONS.md`; all 4 primary hypotheses reported including the honest H4 null; Holm–Bonferroni FWER control enforced. |
| **T5** | **Dependency / Supply-Chain Tampering (`B35`)** (compromised PyPI/crates/third-party upstream or mutated release binaries) | Non-reproducible or malicious build artifacts | Pinned `requirements.txt` (0 open Dependabot alerts, 0 `osv-scanner` CVEs), `engines/rust/Cargo.lock`, `lean/lake-manifest.json`; offline-vendored `third_party/{moonlab,qgtl,quantum_rng}`; SHA-256-verified `osv-scanner` and `gitleaks` in CI; LF-normalized `data/MANIFEST.sha256` bound to DigiCert RFC 3161 `.tsr` + Bitcoin `.ots` + Sigstore SLSA attestations on GitHub Releases. |
| **T6** | **Static Web Portal XSS / Mixed Content / CDN Tracking** | Client-side script injection or broken offline rendering | Zero external CDN dependencies in `web/index.html` and `web/blueprint/index.html`; strict `Content-Security-Policy` meta tag with `script-src 'self'` (external `web/observatory.js`, zero `'unsafe-inline'` scripts) and `script-src 'none'` on the Blueprint page; all dynamic canvas rendering uses numeric state (no `innerHTML`). |
| **T7** | **Secret Leakage (`A24`)** | Exposed API keys or credentials in git history | `.gitleaks.toml` + CI `gitleaks` scan + `.env` ignored in `.gitignore`; zero external API keys required anywhere in the project. |

## 2. Out-of-Scope Threats

- Physical side-channel attacks against host CPUs executing the AVX2/C/Rust engines (no cryptographic secrets are processed).
- Hardware quantum-computer calibration errors (all quantum-mechanical computations here are exact/numerical classical simulations of finite-dimensional Hamiltonians; no physical QPU is accessed).

## 3. Responsible Disclosure

See [`SECURITY.md`](../SECURITY.md) for vulnerability and proof-soundness reporting procedures.
