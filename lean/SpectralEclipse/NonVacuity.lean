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

end SpectralEclipse.NonVacuity
