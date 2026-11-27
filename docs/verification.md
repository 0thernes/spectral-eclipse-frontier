# Verification Matrix & Evidence Tiers

Every quantitative and mathematical claim in `spectral-eclipse-frontier` carries an explicit epistemic tag distinguishing deductive machine-checked proof from exact computation and empirical simulation.

## 1. Epistemic Tier Definitions

| Tag | Meaning | Trust Base |
|---|---|---|
| **`[LEAN-6K]`** | Formally proved in Lean 4.35.0 (`autoImplicit = false`, 0 `sorry`, 0 `native_decide`) and independently replayed by **6 proof checkers** (`lake comparator --config comparator.json --paranoid` inside `bubblewrap` on Linux CI) | Lean 4.35.0 + 5 independent kernel implementations (`leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`), strictly within `[propext, Classical.choice, Quot.sound]` |
| **`[EXACT-COMP]`** | Verified in exact arithmetic with zero rounding error (SymPy Sturm sequences in $\mathbb{Q}[u]$, Zig `std.math.big.int` rational Hochstadt reconstruction, exact algebraic identities) | Python/SymPy and Zig arbitrary-precision rational arithmetic |
| **`[EMPIRICAL]`** | High-precision numerical simulation or pre-registered Monte Carlo statistics (80-digit `mpmath`, IEEE-754 AVX2/C11/C++20/Rust, Eshkol dual-number AD, Moonlab 32-dim Trotter-Suzuki, QGTL/QRNG 30-seed disorder study) | Floating-point / Trotter discretization bounds explicitly measured against exact oracles |

## 2. Complete Theorem & Audit Verification Matrix

| Claim / Theorem | Tier | Lean Module / Target | Non-Vacuity & Adversarial Refutation | Polyglot & Test Cross-Check |
|---|---|---|---|---|
| **Theorems 1–3** ($4\times 4, 5\times 5, 6\times 6$ + universal even converse) | `[LEAN-6K]` | `Chains456.lean` (`target_theorem_{1,2,3}_*`) | `witness_4x4_even_p2`, `refute_4x4_false_p3` | All 8 engines + `test_all.py` + `test_lean_negative.py` |
| **Theorem 4** (Conjecture 4.1 of `arXiv:2507.18767v1`, reduced & unreduced) | `[LEAN-6K]` | `Conjecture41.lean` (`target_theorem_4_*`) | `witness_7x7_{no_ESE,ESE}`, `refute_7x7_bad_threshold` | All 8 engines + Sturm + Zig $\mathbb{Q}$ + 80-digit `mpmath` |
| **Theorem 5** ($8\times 8$ sharp even rupture, $N_{\mathrm{crit}}^{\mathrm{even}} = 8$) | `[LEAN-6K]` | `RuptureAndPhase.lean` (`target_theorem_5_8x8_rupture`) | `witness_8x8_rupture_m1` | All 8 engines + `test_all.py` |
| **Theorem 6** (Critical $9\times 9$ No-ESE Theorem, 19 bivariate Bernstein certs) | `[LEAN-6K]` | `Critical9x9Certs.lean`, `Critical9x9.lean` (`target_theorem_6_critical_9x9`) | `witness_9x9_critical_no_ESE` | All 8 engines + Sturm + Rust exhaustive scan |
| **Theorem 7** ($11\times 11$ exact threshold $m \ge 6 \iff M^* = 12$, 5 global rational SOS certs) | `[LEAN-6K]` | `RuptureAndPhase.lean` (`target_theorem_7_11x11_threshold`) | `witness_11x11_{subcritical_m5,supercritical_m6}`, `refute_11x11_threshold_m5` | All 8 engines + `test_lean_negative.py` |
| **Theorem 8** (Universal $N_{\mathrm{crit}}(R) = 3R + 2$ phase transition) | `[LEAN-6K]` | `RuptureAndPhase.lean` (`target_theorem_8_3R_plus_2`) | `witness_3R2_R2`, `refute_3R2_wrong_formula` | Rust scanner ($R = 1, 2, 3, 4$) + `test_all.py` |
| **Theorem 9** (Infinite non-symmetric staggered-field $5\times 5$ complex ESE family $J_{a,b}$) | `[LEAN-6K]` | `NonSymmetricFamily.lean` (`target_theorem_9_nonsymmetric_family`) | `witness_J14_staggered_complex_ESE`, `refute_5x5_nonsym_no_ESE_assumption` | C++20 complex propagator + Eshkol AD + Moonlab 32-dim WASM ($P_0(\pi/3)=1.29\times 10^{-10}$, $P_4(\pi)=0.9999999857$) |
| **Theorem 10** (Exact QGTL metric $g_{tt} = b_0^2$, Mandelstam–Tamm QSL $\tau \ge \pi/(2b_0)$, ESE–ETE duality) | `[LEAN-6K]` | `SpeedLimitAndDuality.lean` (`target_theorem_10{a,b}_*`) | `witness_J14_qsl_variance`, `refute_qsl_saturation_for_J14` | QGTL C engine + Eshkol AD (`max_diff = 1.332e-15`) + `test_lean_negative.py` |
| **8-Engine Cross-Parity** | `[EXACT-COMP]` / `[EMPIRICAL]` | — | `results/polyglot_parity.json` (`0` mismatches across 13 chains) | `scripts/run_polyglot_parity.py` |
| **Pre-Registered QRNG Study (H1–H4)** | `[EMPIRICAL]` | — | `PREREGISTRATION.md` (`1dac632`) -> `results/qgtl_qrng_analysis.json` (H1–H3 SIG; H4 honest null) | `scripts/analyze_qrng_study.py` + `tests/test_all.py` |

## 3. Quality Assurance Gates

1. **Axiom Audit:** `lean/VerifyAxioms.lean` checks 49 explicit declarations + exhaustive `Lean.collectAxioms` across all **572 theorems** in `SpectralEclipse` (`0` disallowed axioms). Verified verbatim against `README.md` by `scripts/check_readme_axioms.py --require-exhaustive`.
2. **Negative Kernel Tests:** `scripts/test_lean_negative.py` verifies live that the Lean 4.35.0 kernel rejects 3 mutated false theorems (`3/3 PASS`).
3. **Mutation Audit (`B13`):** `scripts/mutation_audit.py` injects 10 single-point source faults into an isolated copy of `python/spectral_eclipse/core.py` and runs `pytest`: **10/10 killed (`100.0%` kill rate, `0` survived)**.
4. **Property-Based & Metamorphic Tests (`B10`, `B14`):** 1,000-case Hypothesis suite in `tests/test_all.py` checking spectral shift & positive rescaling invariance of ESE, plus B20 cancellation guards.
5. **Static Analysis:** `ruff check` (0 errors), `mypy --strict` (0 errors), `cargo clippy -- -D warnings` (0 warnings), C11/C++20 `-Wall -Wextra -Werror`, Batteries `runLinter` (CI), `gitleaks`, and SHA-256-verified `osv-scanner`.
6. **Bibliography Integrity:** `scripts/check_citations.py --live` verifies **15/15** entries live against Crossref / arXiv APIs (`0` retractions, `0` broken DOIs).
