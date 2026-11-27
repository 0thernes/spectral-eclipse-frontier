# Statement-Fidelity Audit

This document maps every mathematical theorem stated in `paper/main.tex` to its exact Lean 4.35.0 definition and theorem in `lean/SpectralEclipse/`, its isolated Mathlib-only target in `lean/Challenge.lean`, its concrete witness in `lean/SpectralEclipse/NonVacuity.lean`, and its machine-checked refutation of false variants in `lean/SpectralEclipse/AdversarialTests.lean`.

| Paper Theorem | Library Theorem (`SpectralEclipse.*`) | Isolated `Challenge.lean` Target | Non-Vacuity Witness | Adversarial Refutation | Fidelity Notes |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Schrödinger Fidelity (§2)** | `schrodinger_solution_fidelity` | Direct definition of `spectralState` | `witness_J14_staggered_complex_ESE` | — | Literal ODE $d\psi_j/dt = -i(J\psi)_j$ on `jacobiMatrix` |
| **Universal Even Converse (Thm. 3.2(1))** | `even_hasESE_of_min_ge_three` | Used inside `target_theorem_{1,3}` | `witness_{4x4,6x6}_ESE_*` | — | Holds for arbitrary even dimension $2n \ge 2$ |
| **Theorem 1 ($4\times 4$)** | `dichotomy_4x4` | `target_theorem_1_4x4` | `witness_4x4_{noESE_1_3,ESE_3_5}` | `mutated_4x4_false_p3` (neg test) | Exact `↔` on reduced `amp4` |
| **Theorem 2 ($5\times 5$)** | `dichotomy_5x5` | `target_theorem_2_5x5` | `witness_5x5_{noESE_1_2,ESE_3_4}` | — | Exact `↔` on reduced `amp5` |
| **Theorem 3 ($6\times 6$)** | `dichotomy_6x6` | `target_theorem_3_6x6` | `witness_6x6_{noESE_1_3_5,ESE_3_5_7}` | — | Exact `↔` on reduced `amp6` |
| **Theorem 4 (Conjecture 4.1, Reduced)** | `conjecture_4_1_7x7` | `target_theorem_4_conjecture_4_1` | `witness_7x7_{noESE_1_2_3,ESE_3_4_5}` | — | Literal match to `arXiv:2507.18767v1` Conj. 4.1 |
| **Theorem 4 (Conjecture 4.1, Unreduced)** | `conjecture_4_1_7x7_unreduced` | `target_theorem_4_conjecture_4_1_unreduced` | Covered via `c=1, g=1` | — | Arbitrary real scale $c>0$ & unreduced $(x,y,z)$ |
| **Theorem 5 ($8\times 8$ Rupture)** | `even_rupture_8x8` | `target_theorem_5_even_rupture_8x8` | `witness_8x8_rupture_m1` | `refute_even_8x8_naive_divisibility` | $\forall m\ge 1$, explicit witness $t_0=2\pi/(4m+5)$ |
| **Theorem 6 (Critical $9\times 9$)** | `odd_critical_9x9_no_ESE` | `target_theorem_6_critical_9x9` | `witness_9x9_noESE_1_{2_3_4,20_21_22}` | — | Universal $\forall 1<b<c<d$ alternating parity |
| **Theorem 7 ($11\times 11$, $M^*=12$)** | `odd_rupture_11x11_threshold` | `target_theorem_7_odd_rupture_11x11` | `witness_11x11_{subcrit_m5,supercrit_m6}` | `refute_odd_11x11_naive_divisibility`, `refute_11x11_threshold_m5` | Exact `↔ (6 ≤ m)` via SOS ($m\le 5$) + deg-8 poly ($m\ge 6$) |
| **Theorem 8 (Universal $3R+2$)** | `universal_phase_transition_3R_plus_2`, `cluster_self_gap_sum` | `target_theorem_8_universal_3R_plus_2` | Exact $R=3 \implies 3\cdot 2^2 = 12$ | — | Exact asymptotic `Tendsto` + critical bound $\le 1/2$ |
| **Theorem 9 (Non-Symmetric $J_{a,b}$)** | `theorem_9_nonsymmetric_family` | `target_theorem_9_nonsymmetric_family` | `witness_J14_staggered_complex_ESE` | `refute_5x5_nonsym_no_ESE_assumption` | Literal $5\times 5$ matrix `stagJacobi`, ODE, PST $\psi_4(\pi)=1$, complex ESE $\psi_0(\pi/3)=0$ |
| **Theorem 10A (QGTL Metric & QSL)** | `jacobi_energy_variance_eq_b0_sq`, `spectral_variance_eq_b0_sq`, `mandelstam_tamm_ese_bound` | `target_theorem_10a_qsl_and_variance` | `witness_J14_qsl_variance` | `refute_qsl_saturation_for_J14` | Arbitrary dimension $n\ge 2$ & arbitrary discrete spectrum |
| **Theorem 10B (ESE–ETE Duality)** | `ese_ete_duality` | `target_theorem_10b_ese_ete_duality` | Direct norm equality on $J_{1,4}$ | — | Exact $\forall t\in\mathbb{R}$ modulus identity |

## Axiom Verification Summary

All 49 explicit `#print axioms` declarations and all **568** theorem constants discovered by the `Lean.collectAxioms` metaprogram in `lean/VerifyAxioms.lean` depend strictly on `[propext, Classical.choice, Quot.sound]` with **0 disallowed axioms** and **0 `sorry`**.
