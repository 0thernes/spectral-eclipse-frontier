/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Chains456
public import SpectralEclipse.Conjecture41
public import SpectralEclipse.RuptureAndPhase
public import SpectralEclipse.Critical9x9
public import SpectralEclipse.NonSymmetricFamily
public import SpectralEclipse.SpeedLimitAndDuality
import Mathlib.Tactic

/-!
# Non-Vacuity Witnesses for Every Theorem Hypothesis Bundle (Theorems 1–10)

Instantiates every single theorem in `SpectralEclipse` with explicit concrete numerical
witnesses so no universal implication can hold vacuously:
  - `4 × 4` `{±1/2, ±3/2}` (No ESE) and `{±3/2, ±5/2}` (ESE)
  - `5 × 5` `{0, ±1, ±2}` (No ESE) and `{0, ±3, ±4}` (ESE)
  - `6 × 6` `{±1/2, ±3/2, ±5/2}` (No ESE) and `{±3/2, ±5/2, ±7/2}` (ESE)
  - `7 × 7` `{0, ±1, ±2, ±3}` (No ESE) and `{0, ±3, ±4, ±5}` (ESE)
  - `8 × 8` `m = 1` `{±1/2, ±7/2, ±9/2, ±11/2}` (rupture ESE)
  - `9 × 9` `{0, ±1, ±2, ±3, ±4}` and `{0, ±1, ±20, ±21, ±22}` (No ESE)
  - `11 × 11` `m = 5` (No ESE) and `m = 6` (rupture ESE)
  - `5 × 5` non-symmetric staggered-field `J_{1,4}` (`a = 1, k = 0`): explicit `a_diag = (4, 6, 4, 6, 4)`,
    `b_0^2 = 15`, exact PST `ψ(π)_4 = 1`, exact complex ESE `ψ(π/3)_0 = 0`, and QSL bound `π/(2√15) ≤ π/3`.
-/

@[expose] public section

namespace SpectralEclipse.NonVacuity

theorem witness_4x4_noESE_1_3 : ¬HasESEReal (amp4 1 3) := by
  have h := dichotomy_4x4 (p := 1) (q := 3) ⟨0, rfl⟩ ⟨1, rfl⟩ (by decide) (by decide)
  simpa using h.mpr rfl

theorem witness_4x4_ESE_3_5 : HasESEReal (amp4 3 5) := by
  have h := dichotomy_4x4 (p := 3) (q := 5) ⟨1, rfl⟩ ⟨2, rfl⟩ (by decide) (by decide)
  by_contra hno
  have : (3 : ℕ) = 1 := h.mp (by simpa using hno)
  omega

theorem witness_5x5_noESE_1_2 : ¬HasESEReal (amp5 1 2) := by
  have h := dichotomy_5x5 (y := 1) (x := 2) ⟨0, rfl⟩ ⟨1, rfl⟩ (by decide) (by decide)
  simpa using h.mpr rfl

theorem witness_5x5_ESE_3_4 : HasESEReal (amp5 3 4) := by
  have h := dichotomy_5x5 (y := 3) (x := 4) ⟨1, rfl⟩ ⟨2, rfl⟩ (by decide) (by decide)
  by_contra hno
  have : (3 : ℕ) = 1 := h.mp (by simpa using hno)
  omega

theorem witness_6x6_noESE_1_3_5 : ¬HasESEReal (amp6 1 3 5) := by
  have h := dichotomy_6x6 (p := 1) (q := 3) (r := 5)
    ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ (by decide) (by decide) (by decide) (by decide)
  simpa using h.mpr rfl

theorem witness_6x6_ESE_3_5_7 : HasESEReal (amp6 3 5 7) := by
  have h := dichotomy_6x6 (p := 3) (q := 5) (r := 7)
    ⟨1, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ (by decide) (by decide) (by decide) (by decide)
  by_contra hno
  have : (3 : ℕ) = 1 := h.mp (by simpa using hno)
  omega

theorem witness_7x7_noESE_1_2_3 : ¬HasESEReal (amp7 1 2 3) := by
  have h := conjecture_4_1_7x7 (x := 1) (y := 2) (z := 3)
    ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨1, rfl⟩ (by decide) (by decide) (by decide)
  simpa using h.mpr ⟨one_dvd 2, one_dvd 3⟩

theorem witness_7x7_ESE_3_4_5 : HasESEReal (amp7 3 4 5) := by
  have h := conjecture_4_1_7x7 (x := 3) (y := 4) (z := 5)
    ⟨1, rfl⟩ ⟨2, rfl⟩ ⟨2, rfl⟩ (by decide) (by decide) (by decide)
  by_contra hno
  have hdiv : 3 ∣ 4 ∧ 3 ∣ 5 := h.mp (by simpa using hno)
  omega

theorem witness_8x8_rupture_m1 : HasESEReal (amp8 1 7 9 11) := by
  have h := (even_rupture_8x8 (m := 1) (by decide)).2
  norm_num at h
  exact h

theorem witness_9x9_noESE_1_2_3_4 : ¬HasESEReal (amp9 1 2 3 4) := by
  rintro ⟨τ, hτ0, hτpi, hzero⟩
  have hpos := odd_critical_9x9_no_ESE (b := 2) (c := 3) (d := 4)
    (by decide) (by decide) (by decide) ⟨1, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ τ hτ0.le hτpi
  norm_num at hpos
  linarith

theorem witness_9x9_noESE_1_20_21_22 : ¬HasESEReal (amp9 1 20 21 22) := by
  rintro ⟨τ, hτ0, hτpi, hzero⟩
  have hpos := odd_critical_9x9_no_ESE (b := 20) (c := 21) (d := 22)
    (by decide) (by decide) (by decide) ⟨10, rfl⟩ ⟨10, rfl⟩ ⟨11, rfl⟩ τ hτ0.le hτpi
  norm_num at hpos
  linarith

theorem witness_11x11_subcrit_m5 : ¬HasESEReal (amp11 1 10 11 12 13) := by
  have h := odd_rupture_11x11_threshold (m := 5) (by decide)
  intro hese
  have h6 : 6 ≤ 5 := h.mp (by norm_num; exact hese)
  omega

theorem witness_11x11_supercrit_m6 : HasESEReal (amp11 1 12 13 14 15) := by
  have h := (odd_rupture_11x11_threshold (m := 6) (by decide)).mpr (by decide)
  norm_num at h
  exact h

theorem witness_J14_staggered_complex_ESE :
    stagDiag 1 4 0 = 4 ∧
    stagDiag 1 4 1 = 6 ∧
    (stagHop 1 4 0) ^ 2 = 15 ∧
    spectralState (stagEigvals 1 4) (stagEigvecs 1 4) Real.pi 4 = 1 ∧
    spectralState (stagEigvals 1 4) (stagEigvecs 1 4) (Real.pi / 3) 0 = 0 := by
  have h := theorem_9_nonsymmetric_family (a := 1) (k := 0) ⟨0, rfl⟩ (by decide)
  norm_num at h
  refine ⟨rfl, ?_, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · simp [stagDiag]; norm_num
  · simp only [stagHop, Matrix.cons_val_zero]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num

theorem witness_J14_qsl_variance :
    (∑ i : Fin 5, ((stagJacobi 1 4) i 0 - (if i = 0 then stagDiag 1 4 0 else 0)) ^ 2) = 15 ∧
    Real.pi / (2 * Real.sqrt 15) < Real.pi / 3 := by
  constructor
  · have h := jacobi_energy_variance_eq_b0_sq (n := 5) (by decide) (stagDiag 1 4) (stagHop 1 4)
    change (∑ i : Fin 5, ((stagJacobi 1 4) i 0 - (if i = 0 then stagDiag 1 4 0 else 0)) ^ 2) =
      (stagHop 1 4 0) ^ 2 at h
    rw [h]
    simp only [stagHop, Matrix.cons_val_zero]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  · have hrt : (3 : ℝ) < 2 * Real.sqrt 15 := by
      have hsq : (9 : ℝ) < (2 * Real.sqrt 15) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg 15]
    exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hrt

/-- Non-vacuity witness for unreduced real-scaled Conjecture 4.1 (`c = 2`, `(x,y,z) = (3,6,9)`,
`g = 3`, `T₀ = π/6`, `3 ∣ 6 ∧ 3 ∣ 9` -> no ESE on `(0, π/6)`). -/
theorem witness_7x7_unreduced_c2_3_6_9 :
    ∀ τ : ℝ, 0 < τ → τ < Real.pi / 6 → amp7 6 12 18 τ ≠ 0 := by
  have h := (conjecture_4_1_7x7_unreduced (c := 2) (by norm_num) (x := 3) (y := 6) (z := 9)
    ⟨1, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩ (by decide) (by decide)).mpr ⟨by decide, by decide⟩
  have hgcd : Nat.gcd 3 (Nat.gcd 6 9) = 3 := by decide
  rw [hgcd] at h
  norm_num at h
  exact h

/-- Non-vacuity witness for Theorem 8 (`universal_phase_transition_3R_plus_2` at `R = 3`) and
`cluster_self_gap_sum` at `r = 4`, proving `Φ(3, 4, 12) = 1`. -/
theorem witness_universal_3R_plus_2_R3 :
    clusterToCoreRatio 3 3 12 = 1 / 4 ∧
    clusterToCoreRatio 3 4 12 = 1 ∧
    ∑ j ∈ Finset.range 4, (1 : ℝ) / ((j.factorial : ℝ) * ((4 - 1 - j).factorial : ℝ)) = 4 / 3 := by
  have h8 := universal_phase_transition_3R_plus_2 (R := 3) (by decide)
  have hcrit := (h8.2.1 12 (by norm_num)).1
  have hsup := h8.2.2.2.1 12 (by norm_num)
  norm_num at hcrit hsup
  refine ⟨hcrit, hsup, ?_⟩
  rw [cluster_self_gap_sum 4 (by decide)]
  norm_num [Nat.factorial]

/-- Non-vacuity witness for Theorem 10B (`ese_ete_duality`) instantiated on `J_{1,4}` at `t = π/3`,
proving exact Early Target Exclusion `targetAmpComplex _ (stagEigvals 1 4) (stagEigvecs 1 4) (2π/3) = 0`. -/
theorem witness_J14_ese_ete_duality :
    Complex.normSq
      (targetAmpComplex (n := 5) (by decide) (stagEigvals 1 4) (stagEigvecs 1 4) (2 * Real.pi / 3)) = 0 := by
  have hparity : ∀ k : Fin 5,
      stagEigvecs 1 4 k ⟨5 - 1, by decide⟩ = (-1 : ℝ) ^ (k : ℕ) * stagEigvecs 1 4 k ⟨0, by decide⟩ := by
    intro k
    fin_cases k <;> (simp [stagEigvecs, neg_div]; try norm_num)
  have hpst : ∀ k : Fin 5,
      Complex.exp (-Complex.I * (stagEigvals 1 4 k : ℂ) * (Real.pi : ℂ)) =
        (1 : ℂ) * (-1 : ℂ) ^ (k : ℕ) := by
    have hexp_even : ∀ m : ℕ,
        Complex.exp (-Complex.I * ((2 * m : ℕ) : ℂ) * (Real.pi : ℂ)) = 1 := by
      intro m
      have : -Complex.I * ((2 * m : ℕ) : ℂ) * (Real.pi : ℂ) =
          ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have hexp_odd : ∀ m : ℕ,
        Complex.exp (-Complex.I * ((2 * m + 1 : ℕ) : ℂ) * (Real.pi : ℂ)) = -1 := by
      intro m
      have : -Complex.I * ((2 * m + 1 : ℕ) : ℂ) * (Real.pi : ℂ) =
          -(Real.pi * Complex.I) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
          Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    intro k
    fin_cases k
    · dsimp only; simp [stagEigvals]
    · dsimp only; simpa [stagEigvals] using hexp_odd 0
    · dsimp only; simpa [stagEigvals] using hexp_even 2
    · dsimp only
      have h9 : (stagEigvals 1 4 3 : ℂ) = ((2 * 4 + 1 : ℕ) : ℂ) := by norm_num [stagEigvals]
      change Complex.exp (-Complex.I * (stagEigvals 1 4 3 : ℂ) * ↑Real.pi) = 1 * (-1 : ℂ) ^ (3 : ℕ)
      rw [h9, hexp_odd 4]; norm_num
    · dsimp only
      have h10 : (stagEigvals 1 4 4 : ℂ) = ((2 * 5 : ℕ) : ℂ) := by norm_num [stagEigvals]
      change Complex.exp (-Complex.I * (stagEigvals 1 4 4 : ℂ) * ↑Real.pi) = 1 * (-1 : ℂ) ^ (4 : ℕ)
      rw [h10, hexp_even 5]; norm_num
  have hdual := ese_ete_duality (n := 5) (by decide) (stagEigvals 1 4) (stagEigvecs 1 4)
    Real.pi 1 (by simp) hparity hpst (Real.pi / 3)
  have htime : Real.pi - Real.pi / 3 = 2 * Real.pi / 3 := by ring
  rw [htime] at hdual
  rw [hdual]
  have hfid := schrodinger_solution_fidelity (n := 5) (by decide)
    (stagJacobi 1 4) (stagEigvals 1 4) (stagEigvecs 1 4)
    (stagJacobi_eigpairs (by norm_num) (by norm_num))
    (stagJacobi_init_complete (by norm_num) (by norm_num))
  have hret := hfid.2.2.1 (Real.pi / 3)
  have hzero : spectralState (stagEigvals 1 4) (stagEigvecs 1 4) (Real.pi / 3) ⟨0, by decide⟩ = 0 :=
    witness_J14_staggered_complex_ESE.2.2.2.2
  rw [← hret, hzero, map_zero]

end SpectralEclipse.NonVacuity
