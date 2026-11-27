# Claims Registry & Explicit Falsification Protocol

Every scientific, mathematical, and empirical claim in **The Spectral Eclipse Frontier** is enumerated below with its exact verification tag, executable verification command, and concrete falsification criterion (**What Would Prove Us Wrong**).

## Verification Tag Taxonomy

- **`[LEAN-6K]`**: Machine-checked inside the Lean 4.35.0 kernel (`autoImplicit = false`, zero `sorry`, zero custom axioms, strictly `[propext, Classical.choice, Quot.sound]`), backed by isolated Mathlib-only `Challenge.lean` / `Solution.lean` targets replayed across six independent checker runs (`lake comparator --config comparator.json --paranoid`).
- **`[EXACT-COMP]`**: Verified by exact rational arithmetic over $\mathbb{Q}$ (`reference/exact_oracle.py` SymPy square-free Sturm root isolation, `engines/zig` arbitrary-precision rational Hochstadt engine) or exhaustive deterministic integer scans (`engines/rust`, `engines/cpp`).
- **`[EMPIRICAL]`**: Pre-registered computational experiment locked in `PREREGISTRATION.md` (commit `1dac632`) before data generation, analyzed via paired permutation tests and Holm–Bonferroni FWER control.

## Master Claims Table (C1–C12)

| Claim | Statement | Tag | Primary Evidence / Artifact | Falsification Condition (What Would Prove Us Wrong) |
| :--- | :--- | :--- | :--- | :--- |
| **C1** | Complete $4\times 4$ dichotomy: $\neg\mathrm{ESE}\iff p=1$ | `[LEAN-6K]` | `SpectralEclipse.dichotomy_4x4` (`target_theorem_1_4x4`) | A reduced $4\times 4$ PST chain with $p=1$ exhibiting $A_4(\tau)=0$ on $(0,\pi)$, or $p\ge 3$ remaining strictly positive on $(0,\pi)$. |
| **C2** | Complete $5\times 5$ dichotomy: $\neg\mathrm{ESE}\iff y=1$ | `[LEAN-6K]` | `SpectralEclipse.dichotomy_5x5` (`target_theorem_2_5x5`) | A reduced $5\times 5$ symmetric PST chain violating $\neg\mathrm{ESE}\iff y=1$. |
| **C3** | Complete $6\times 6$ even dichotomy: $\neg\mathrm{ESE}\iff p=1$ + universal even converse | `[LEAN-6K]` | `SpectralEclipse.dichotomy_6x6`, `even_hasESE_of_min_ge_three` | Any $6\times 6$ chain with $p=1$ crossing zero on $(0,\pi)$, or any even $2n$ chain with $p_1\ge 3$ avoiding zero. |
| **C4** | Complete resolution of **Conjecture 4.1** (`arXiv:2507.18767v1`), reduced & unreduced real-scaled | `[LEAN-6K]` | `conjecture_4_1_7x7`, `conjecture_4_1_7x7_unreduced` | Any $7\times 7$ symmetric PST chain with $x\mid y, x\mid z$ having ESE, or with $x\nmid y$ or $x\nmid z$ avoiding ESE. |
| **C5** | Sharp even rupture at $N_{\mathrm{crit}}^{\mathrm{even}} = 8$ ($\forall m \ge 1$) | `[LEAN-6K]` | `SpectralEclipse.even_rupture_8x8` | Any integer $m\ge 1$ for which $A_8(1, 4m+3, 4m+5, 4m+7; 2\pi/(4m+5)) \ge 0$. |
| **C6** | **Critical $9\times 9$ No-ESE Theorem**: $\forall 1<b<c<d$ alternating parity, $A_9(1,b,c,d;t)>0$ on $[0,\pi)$ | `[LEAN-6K]` | `SpectralEclipse.odd_critical_9x9_no_ESE` + 19 Bernstein certs | Any alternating-parity triple $(b,c,d)$ with $1<b<c<d$ and any $t\in[0,\pi)$ with $A_9(1,b,c,d;t)\le 0$. |
| **C7** | Sharp odd rupture at $N_{\mathrm{crit}}^{\mathrm{odd}} = 11$: $S(m)$ has ESE $\iff m\ge 6$ ($M^*=12$) | `[LEAN-6K]` | `SpectralEclipse.odd_rupture_11x11_threshold` | Any $m\in\{1..5\}$ crossing zero on $(0,\pi)$ or any $m\ge 6$ remaining nonnegative on $(0,\pi)$. |
| **C8** | Universal $(R,r)$ phase transition at $r_{\mathrm{crit}}(R)=R+1$, $N_{\mathrm{crit}}(R)=3R+2$ | `[LEAN-6K]` | `universal_phase_transition_3R_plus_2`, `cluster_self_gap_sum` | Failure of $\Phi(R,r,M)$ to vanish for $r<R$, stabilize at $2^{-(R-1)}$ for $r=R$, or diverge for $r\ge R+1$. |
| **C9** | Infinite non-symmetric staggered-field $5\times 5$ complex ESE family $J_{a,b}$ | `[LEAN-6K]` | `theorem_9_nonsymmetric_family` | Any odd $a$ ($3\nmid a$) and $b=a+6k+3$ where $J_{a,b}$ fails persymmetry, PST $\psi_4(\pi)=1$, or complex ESE $\psi_0(\pi/3)=0\in\mathbb{C}$. |
| **C10** | Exact QGTL metric $g_{tt}=b_0^2$, Mandelstam–Tamm QSL $\tau\ge\pi/(2|b_0|)$, & ESE–ETE duality | `[LEAN-6K]` | `jacobi_energy_variance_eq_b0_sq`, `mandelstam_tamm_ese_bound`, `ese_ete_duality` | Any real Jacobi chain with $\mathrm{Var}_{e_0}(J)\ne b_0^2$, any ESE time $\tau < \pi/(2|b_0|)$, or any PST chain breaking $|\psi_{N-1}(T_0-t)|=|\psi_0(t)|$. |
| **C11** | Finite-$M$ critical thresholds $M^*(4)=30$ ($N=14$), $M^*(5)=78$ ($N=17$) | `[EXACT-COMP]` | `engines/rust/src/main.rs`, `engines/cpp/se_propagator.cpp` | Exact Sturm root count disagreeing with $m=15$ ($N=14$) or $m=39$ ($N=17$). |
| **C12** | Pre-registered QRNG static-disorder study: H1–H3 significant ($p_{\mathrm{Holm}}\le 0.0008$), H4 null ($p_{\mathrm{Holm}}=0.988$) | `[EMPIRICAL]` | `PREREGISTRATION.md`, `results/qgtl_qrng_analysis.json` | Independent re-execution of `engines/qgtl_qrng/se_qgtl_qrng` + `scripts/analyze_qrng_study.py` yielding contradictory statistics or contradicting Holm FWER verdicts. |

## Explicit Falsification Protocol (How to Attack This Repo)

1. **Formal Proof Attack:** Inspect `lean/Challenge.lean` (280 lines, Mathlib-only) line by line to confirm definitions match textbook Jacobi matrices, Schrödinger evolution, and Hochstadt amplitudes; then run `cd lean && lake comparator --config comparator.json --paranoid` and `lake env lean VerifyAxioms.lean`.
2. **Definition-Fidelity Attack:** Inspect `lean/SpectralEclipse/NonVacuity.lean` and `lean/SpectralEclipse/AdversarialTests.lean`, and run `python scripts/test_lean_negative.py`.
3. **Numerical / Physical Attack:** Run `python scripts/run_polyglot_parity.py` to independently compare all 8 engines (including full 32-dim 5-qubit Moonlab WASM and zero-float Zig $\mathbb{Q}$) against the 80-digit Sturm oracle.
4. **Mutation Attack:** Run `python scripts/mutation_audit.py` to verify 10/10 semantic mutants are killed by `tests/test_all.py`.
