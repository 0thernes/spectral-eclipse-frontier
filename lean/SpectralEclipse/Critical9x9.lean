/-
Copyright (c) 2026 Alexander Stephen Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Stephen Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander Stephen Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Defs
public import SpectralEclipse.TrigBounds
public import SpectralEclipse.Critical9x9Certs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Theorem 6: Complete Resolution of the Critical `9 × 9` Odd Symmetric Chain (NO ESE)

Proves that for EVERY `9 × 9` symmetric PST Jacobi chain with spectrum
`{0, ±1, ±b, ±c, ±d}` (`1 < b < c < d`, alternating parity: `b` even, `c` odd, `d` even),
the return amplitude `amp9 1 b c d t` is strictly positive for ALL `t ∈ [0, π)`.
Combined with Theorem 7 (`11 × 11` sharp threshold `M* = 12`), this pins down the EXACT
odd rupture dimension `N_crit^odd = 11`!
-/

@[expose] public section

open scoped BigOperators
open intervalIntegral

namespace SpectralEclipse

/-! ### 1. Second Divided Difference `H2dd` and Confluent Difference `Hww` -/

/-- Confluent second divided difference `H[a, w, w] = (H(a) - H(w) + (w - a) H'(w)) / (w - a)²`. -/
noncomputable def Hww (a w : ℝ) : ℝ :=
  (H a - H w + (w - a) * HDeriv w) / (w - a) ^ 2

/-- Second divided difference `H2dd w0 w1 w = ((H w0 - H w1)/(w1 - w0) - (H w0 - H w)/(w - w0)) / (w - w1)`. -/
noncomputable def H2dd (w0 w1 w : ℝ) : ℝ :=
  ((H w0 - H w1) / (w1 - w0) - (H w0 - H w) / (w - w0)) / (w - w1)

private theorem hasDerivAt_H2dd {w0 w1 w : ℝ} (hw0 : 0 < w0) (hw01 : w0 < w1) (hw1w : w1 < w) :
    HasDerivAt (H2dd w0 w1) ((Hww w1 w - Hww w0 w) / (w1 - w0)) w := by
  have hw_pos : 0 < w := lt_trans (lt_trans hw0 hw01) hw1w
  have h10 : w1 - w0 ≠ 0 := (sub_pos.mpr hw01).ne'
  have hw0_ne : w - w0 ≠ 0 := (sub_pos.mpr (lt_trans hw01 hw1w)).ne'
  have hw1_ne : w - w1 ≠ 0 := (sub_pos.mpr hw1w).ne'
  have hS : HasDerivAt (fun v => (H w0 - H v) / (v - w0)) (-Hww w0 w) w := by
    have h1 := ((hasDerivAt_const w (H w0)).fun_sub (hasDerivAt_H hw_pos)).fun_div
      ((hasDerivAt_id' w).sub_const w0) hw0_ne
    refine h1.congr_deriv ?_
    unfold Hww
    field_simp [hw0_ne]
    ring
  have hnum : HasDerivAt (fun v => (H w0 - H w1) / (w1 - w0) - (H w0 - H v) / (v - w0))
      (0 - (-Hww w0 w)) w :=
    (hasDerivAt_const w ((H w0 - H w1) / (w1 - w0))).fun_sub hS
  have hdiv := hnum.fun_div ((hasDerivAt_id' w).sub_const w1) hw1_ne
  refine hdiv.congr_deriv ?_
  unfold Hww
  field_simp [h10, hw0_ne, hw1_ne]
  ring

private theorem hasDerivAt_Hww_left {a w : ℝ} (ha : 0 < a) (haw : a < w) :
    HasDerivAt (fun v => Hww v w)
      (((w - a) * (HDeriv a + HDeriv w) + 2 * (H a - H w)) / (w - a) ^ 3) a := by
  have hne : w - a ≠ 0 := (sub_pos.mpr haw).ne'
  have h1 := (hasDerivAt_H ha).sub_const (H w)
  have h2 := ((hasDerivAt_const a w).fun_sub (hasDerivAt_id' a)).mul_const (HDeriv w)
  have hnum := h1.fun_add h2
  have hden : HasDerivAt (fun i => (w - i) ^ 2) (↑2 * (w - a) ^ (2 - 1) * (0 - 1)) a :=
    ((hasDerivAt_const a w).fun_sub (hasDerivAt_id' a)).pow 2
  have hdiv := hnum.fun_div hden (pow_ne_zero 2 hne)
  refine hdiv.congr_deriv ?_
  field_simp [hne]
  ring

/-! ### 2. Case 0 (`√w ≤ 83/20`) via `HDeriv3_neg` -/

private theorem Hww_strictAnti_case0 {w a1 a2 : ℝ} (ha1 : 0 < a1) (ha12 : a1 < a2) (ha2w : a2 < w)
    (hw_le : Real.sqrt w ≤ 83 / 20) :
    Hww a2 w < Hww a1 w := by
  let N : ℝ → ℝ := fun a => (w - a) * (HDeriv a + HDeriv w) + 2 * (H a - H w)
  let N1 : ℝ → ℝ := fun a => (w - a) * HDeriv2 a + (HDeriv a - HDeriv w)
  have hN_deriv : ∀ a, 0 < a → HasDerivAt N (N1 a) a := by
    intro a ha
    have h1 := ((hasDerivAt_const a w).fun_sub (hasDerivAt_id' a)).fun_mul
      ((hasDerivAt_HDeriv ha).add_const (HDeriv w))
    have h2 := ((hasDerivAt_H ha).sub_const (H w)).const_mul (2 : ℝ)
    refine (h1.fun_add h2).congr_deriv ?_
    simp only [N1]; ring
  have hN1_deriv : ∀ a, 0 < a → HasDerivAt N1 ((w - a) * HDeriv3 a) a := by
    intro a ha
    have h1 := ((hasDerivAt_const a w).fun_sub (hasDerivAt_id' a)).fun_mul (hasDerivAt_HDeriv2 ha)
    have h2 := (hasDerivAt_HDeriv ha).sub_const (HDeriv w)
    refine (h1.fun_add h2).congr_deriv ?_
    ring
  have hN_neg : ∀ a, 0 < a → a < w → N a < 0 := by
    intro a ha haw
    have hN1_anti : StrictAntiOn N1 (Set.Icc a w) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc a w) ?_ ?_
      · intro v hv
        exact (hN1_deriv v (lt_of_lt_of_le ha hv.1)).continuousAt.continuousWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        have hv0 : 0 < v := lt_trans ha hv.1
        rw [(hN1_deriv v hv0).deriv]
        have hsqv : Real.sqrt v ≤ 83 / 20 := le_trans (Real.sqrt_le_sqrt hv.2.le) hw_le
        have h3 := HDeriv3_neg (Real.sqrt_pos.mpr hv0) hsqv
        rw [Real.sq_sqrt hv0.le] at h3
        exact mul_neg_of_pos_of_neg (sub_pos.mpr hv.2) h3
    have hN_mono : StrictMonoOn N (Set.Icc a w) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc a w) ?_ ?_
      · intro v hv
        exact (hN_deriv v (lt_of_lt_of_le ha hv.1)).continuousAt.continuousWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        have hv0 : 0 < v := lt_trans ha hv.1
        rw [(hN_deriv v hv0).deriv]
        have hgt := hN1_anti ⟨hv.1.le, hv.2.le⟩ (Set.right_mem_Icc.mpr haw.le) hv.2
        simp only [N1, sub_self, zero_mul, add_zero] at hgt
        exact hgt
    have hlt := hN_mono (Set.left_mem_Icc.mpr haw.le) (Set.right_mem_Icc.mpr haw.le) haw
    simp only [N, sub_self, zero_mul, mul_zero, add_zero] at hlt
    exact hlt
  have hanti : StrictAntiOn (fun v => Hww v w) (Set.Icc a1 a2) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a1 a2) ?_ ?_
    · intro v hv
      exact (hasDerivAt_Hww_left (lt_of_lt_of_le ha1 hv.1)
        (lt_of_le_of_lt hv.2 ha2w)).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      have hv0 : 0 < v := lt_trans ha1 hv.1
      have hvw : v < w := lt_trans hv.2 ha2w
      rw [(hasDerivAt_Hww_left hv0 hvw).deriv]
      exact div_neg_of_neg_of_pos (hN_neg v hv0 hvw) (pow_pos (sub_pos.mpr hvw) 3)
  exact hanti (Set.left_mem_Icc.mpr ha12.le) (Set.right_mem_Icc.mpr ha12.le) ha12

/-! ### 3. Case 1 (`√w ≥ 83/20`, `√x₁ ≤ 5/2`) via Cosine Transforms + `cert_case1_bernstein` -/

private theorem H_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ H w := by
  simp only [H, hw.ne', ↓reduceIte]
  have h := Real.cos_le_one (2 * Real.sqrt w)
  exact div_nonneg (by linarith) (by positivity)

private theorem HDeriv_le_one_div_140 {w : ℝ} (hw : 83 / 20 ≤ Real.sqrt w) :
    HDeriv w ≤ 1 / 140 := by
  set x := Real.sqrt w
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := by
    have : 0 < x ^ 2 := sq_pos_of_pos hx0
    have hnn : 0 ≤ w := by
      by_contra hneg; push Not at hneg
      have : Real.sqrt w = 0 := Real.sqrt_eq_zero_of_nonpos hneg.le
      linarith
    rwa [Real.sq_sqrt hnn] at this
  have hxw : x ^ 2 = w := Real.sq_sqrt hw0.le
  unfold HDeriv
  change (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) / (2 * w ^ 2) ≤ 1 / 140
  have hsin : Real.sin (2 * x) ≤ 1 := Real.sin_le_one _
  have hcos : Real.cos (2 * x) ≤ 1 := Real.cos_le_one _
  have hnum : x * Real.sin (2 * x) + Real.cos (2 * x) - 1 ≤ x := by nlinarith
  have hstep : (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) / (2 * w ^ 2) ≤ x / (2 * w ^ 2) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have htail : x / (2 * w ^ 2) ≤ 1 / 140 := by
    rw [← hxw, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hx3 : (83 / 20 : ℝ) ^ 3 ≤ x ^ 3 := by nlinarith
    have hx4 : (x ^ 2) ^ 2 = x * x ^ 3 := by ring
    nlinarith
  linarith

private theorem H_sq_eq_integral {x : ℝ} (hx : 0 < x) :
    H (x ^ 2) = ∫ s in (0 : ℝ)..1, (2 - 2 * s) * Real.cos (2 * x * s) := by
  let a : ℝ := 2 * x
  have ha : a ≠ 0 := by positivity
  let F : ℝ → ℝ := fun s => ((2 - 2 * s) / a) * Real.sin (a * s) - (2 / a ^ 2) * Real.cos (a * s)
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F ((2 - 2 * s) * Real.cos (a * s)) s := by
    intro s _
    have h1 := ((hasDerivAt_const s (2 : ℝ)).fun_sub ((hasDerivAt_id' s).const_mul 2)).div_const a
    have has_d : HasDerivAt (fun t : ℝ => a * t) (a * 1) s := (hasDerivAt_id' s).const_mul a
    have hsin := (Real.hasDerivAt_sin (a * s)).comp s has_d
    have hcos := (Real.hasDerivAt_cos (a * s)).comp s has_d
    refine ((h1.fun_mul hsin).fun_sub (hcos.const_mul (2 / a ^ 2))).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp [ha]
    ring
  have hint : IntervalIntegrable (fun s : ℝ => (2 - 2 * s) * Real.cos (a * s))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  change H (x ^ 2) = ∫ s in (0 : ℝ)..1, (2 - 2 * s) * Real.cos (a * s)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F, a, H, (sq_pos_of_pos hx).ne', ↓reduceIte, Real.sqrt_sq hx.le,
    mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [hx.ne']
  ring

private noncomputable def K1 (s : ℝ) : ℝ :=
  1 / 3 - s ^ 2 + 2 / 3 * s ^ 3

private theorem K1_nonneg {s : ℝ} (hs0 : 0 ≤ s) (_hs1 : s ≤ 1) : 0 ≤ K1 s := by
  have heq : K1 s = (1 - s) ^ 2 * (1 + 2 * s) / 3 := by unfold K1; ring
  rw [heq]; positivity

private theorem neg_HDeriv_sq_eq_integral {x : ℝ} (hx : 0 < x) :
    -HDeriv (x ^ 2) = 2 * ∫ s in (0 : ℝ)..1, K1 s * Real.cos (2 * x * s) := by
  let a : ℝ := 2 * x
  have ha : a ≠ 0 := by positivity
  let A : ℝ → ℝ := fun s => (1 / 3 - s ^ 2 + 2 / 3 * s ^ 3) / a - (-2 + 4 * s) / a ^ 3
  let B : ℝ → ℝ := fun s => (-2 * s + 2 * s ^ 2) / a ^ 2 - 4 / a ^ 4
  let F : ℝ → ℝ := fun s => A s * Real.sin (a * s) + B s * Real.cos (a * s)
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (K1 s * Real.cos (a * s)) s := by
    intro s _
    have hA : HasDerivAt A ((-2 * s + 2 * s ^ 2) / a - 4 / a ^ 3) s := by
      have ha1 := (((hasDerivAt_const s (1 / 3 : ℝ)).fun_sub (hasDerivAt_pow 2 s)).fun_add
        ((hasDerivAt_pow 3 s).const_mul (2 / 3))).div_const a
      have ha2 := ((hasDerivAt_const s (-2 : ℝ)).fun_add ((hasDerivAt_id' s).const_mul 4)).div_const (a ^ 3)
      refine (ha1.fun_sub ha2).congr_deriv ?_; ring
    have hB : HasDerivAt B ((-2 + 4 * s) / a ^ 2) s := by
      have hb1 := (((hasDerivAt_id' s).const_mul (-2 : ℝ)).fun_add
        ((hasDerivAt_pow 2 s).const_mul 2)).div_const (a ^ 2)
      have hb2 : HasDerivAt (fun _ : ℝ => (4 : ℝ) / a ^ 4) 0 s := hasDerivAt_const s _
      refine (hb1.fun_sub hb2).congr_deriv ?_; ring
    have has_d : HasDerivAt (fun t : ℝ => a * t) (a * 1) s := (hasDerivAt_id' s).const_mul a
    have hsin := (Real.hasDerivAt_sin (a * s)).comp s has_d
    have hcos := (Real.hasDerivAt_cos (a * s)).comp s has_d
    refine ((hA.fun_mul hsin).fun_add (hB.fun_mul hcos)).congr_deriv ?_
    simp only [A, B, K1, Function.comp_apply]; field_simp [ha]; ring
  have hint : IntervalIntegrable (fun s : ℝ => K1 s * Real.cos (a * s))
      MeasureTheory.volume 0 1 := by
    have hK1c : Continuous K1 := by unfold K1; fun_prop
    exact (hK1c.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  change -HDeriv (x ^ 2) = 2 * ∫ s in (0 : ℝ)..1, K1 s * Real.cos (a * s)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F, A, B, a, HDeriv, Real.sqrt_sq hx.le, mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [hx.ne']
  ring

private theorem taylorCos5_ub {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.cos θ ≤ 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 := by
  have h := (taylor_trig_bounds 2).1 θ hθ
  simp only [taylorCos, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Nat.factorial] at h
  norm_num at h
  linarith

private theorem int_pow01 (k : ℕ) : ∫ s in (0 : ℝ)..1, s ^ k = 1 / ((k : ℝ) + 1) := by
  rw [integral_pow]; simp

private theorem int_K1_pow (m : ℕ) :
    ∫ s in (0 : ℝ)..1, K1 s * s ^ m =
      1 / 3 * (1 / ((m : ℝ) + 1)) - 1 / ((m : ℝ) + 3) + 2 / 3 * (1 / ((m : ℝ) + 4)) := by
  have hexp : ∀ s : ℝ, K1 s * s ^ m =
      (1 / 3 : ℝ) * s ^ m + (-1 : ℝ) * s ^ (m + 2) + (2 / 3 : ℝ) * s ^ (m + 3) := by
    intro s; unfold K1; ring
  simp_rw [hexp]
  repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  simp_rw [intervalIntegral.integral_const_mul, int_pow01]
  push_cast; ring

private theorem H_le_poly5 {a : ℝ} (ha : 0 < a) :
    H a ≤ 1 * a ^ 0 + (-1 / 3) * a ^ 1 + (2 / 45) * a ^ 2 +
      (-1 / 315) * a ^ 3 + (2 / 14175) * a ^ 4 := by
  set x := Real.sqrt a
  have hx0 : 0 < x := Real.sqrt_pos.mpr ha
  have hxa : x ^ 2 = a := Real.sq_sqrt ha.le
  rw [← hxa, H_sq_eq_integral hx0]
  have hmono :
      ∫ s in (0 : ℝ)..1, (2 - 2 * s) * Real.cos (2 * x * s) ≤
      ∫ s in (0 : ℝ)..1, (2 - 2 * s) *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 -
          (2 * x * s) ^ 6 / 720 + (2 * x * s) ^ 8 / 40320) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s hs => ?_
    · exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact mul_le_mul_of_nonneg_left
        (taylorCos5_ub (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * x) hs.1)) (by linarith [hs.2])
  have heval :
      ∫ s in (0 : ℝ)..1, (2 - 2 * s) *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 -
          (2 * x * s) ^ 6 / 720 + (2 * x * s) ^ 8 / 40320) =
      1 * (x ^ 2) ^ 0 + (-1 / 3) * (x ^ 2) ^ 1 + (2 / 45) * (x ^ 2) ^ 2 +
        (-1 / 315) * (x ^ 2) ^ 3 + (2 / 14175) * (x ^ 2) ^ 4 := by
    have hexp : ∀ s : ℝ, (2 - 2 * s) *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 -
          (2 * x * s) ^ 6 / 720 + (2 * x * s) ^ 8 / 40320) =
        (2 : ℝ) * s ^ 0 + (-2 : ℝ) * s ^ 1 + (-4 * x ^ 2) * s ^ 2 + (4 * x ^ 2) * s ^ 3 +
        (4 / 3 * x ^ 4) * s ^ 4 + (-4 / 3 * x ^ 4) * s ^ 5 +
        (-8 / 45 * x ^ 6) * s ^ 6 + (8 / 45 * x ^ 6) * s ^ 7 +
        (4 / 315 * x ^ 8) * s ^ 8 + (-4 / 315 * x ^ 8) * s ^ 9 := fun s => by ring
    simp_rw [hexp]
    repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, int_pow01]
    norm_num; ring
  linarith

private theorem poly6_le_neg_HDeriv {a : ℝ} (ha : 0 < a) :
    (1 / 3) * a ^ 0 + (-4 / 45) * a ^ 1 + (1 / 105) * a ^ 2 +
      (-8 / 14175) * a ^ 3 + (2 / 93555) * a ^ 4 + (-8 / 14189175) * a ^ 5 ≤ -HDeriv a := by
  set x := Real.sqrt a
  have hx0 : 0 < x := Real.sqrt_pos.mpr ha
  have hxa : x ^ 2 = a := Real.sq_sqrt ha.le
  rw [← hxa, neg_HDeriv_sq_eq_integral hx0]
  have hmono :
      ∫ s in (0 : ℝ)..1, K1 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800) ≤
      ∫ s in (0 : ℝ)..1, K1 s * Real.cos (2 * x * s) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s hs => ?_
    · unfold K1; exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · unfold K1; exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact mul_le_mul_of_nonneg_left
        (taylorCos6_le_cos (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * x) hs.1)) (K1_nonneg hs.1 hs.2)
  have heval :
      2 * ∫ s in (0 : ℝ)..1, K1 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800) =
      (1 / 3) * (x ^ 2) ^ 0 + (-4 / 45) * (x ^ 2) ^ 1 + (1 / 105) * (x ^ 2) ^ 2 +
        (-8 / 14175) * (x ^ 2) ^ 3 + (2 / 93555) * (x ^ 2) ^ 4 +
        (-8 / 14189175) * (x ^ 2) ^ 5 := by
    have hsplit : ∀ s : ℝ, K1 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800) =
        (1 : ℝ) * (K1 s * s ^ 0) + (-(2 * x) ^ 2 / 2) * (K1 s * s ^ 2) +
        ((2 * x) ^ 4 / 24) * (K1 s * s ^ 4) + (-(2 * x) ^ 6 / 720) * (K1 s * s ^ 6) +
        ((2 * x) ^ 8 / 40320) * (K1 s * s ^ 8) +
        (-(2 * x) ^ 10 / 3628800) * (K1 s * s ^ 10) := fun s => by ring
    simp_rw [hsplit]
    have hK1c : Continuous K1 := by unfold K1; fun_prop
    repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, int_K1_pow]
    norm_num; ring
  linarith

/-- Case 1: For EVERY `√w ≥ 83/20`, `a ↦ Hww a w` is strictly decreasing on `(0, 25/4]`. -/
private theorem Hww_strictAnti_case1 {w a1 a2 : ℝ} (ha1 : 0 < a1) (ha12 : a1 < a2)
    (ha2 : a2 ≤ 25 / 4) (hw : 83 / 20 ≤ Real.sqrt w) :
    Hww a2 w < Hww a1 w := by
  have hw_ge : (6889 / 400 : ℝ) ≤ w := by
    have hsq : (83 / 20 : ℝ) ^ 2 ≤ Real.sqrt w ^ 2 := by nlinarith
    have hnn : 0 ≤ w := by
      by_contra hneg; push Not at hneg
      have : Real.sqrt w = 0 := Real.sqrt_eq_zero_of_nonpos hneg.le
      linarith
    rw [Real.sq_sqrt hnn] at hsq
    linarith
  have hw0 : 0 < w := by linarith
  have hHw : 0 ≤ H w := H_nonneg hw0
  have hHpw : HDeriv w ≤ 1 / 140 := HDeriv_le_one_div_140 hw
  have hanti : StrictAntiOn (fun v => Hww v w) (Set.Icc a1 a2) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a1 a2) ?_ ?_
    · intro v hv
      exact (hasDerivAt_Hww_left (lt_of_lt_of_le ha1 hv.1)
        (by linarith [hv.2, ha2, hw_ge])).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      have hv0 : 0 < v := lt_trans ha1 hv.1
      have hv25 : v ≤ 25 / 4 := le_trans hv.2.le ha2
      have hvw : v < w := by linarith
      rw [(hasDerivAt_Hww_left hv0 hvw).deriv]
      refine div_neg_of_neg_of_pos ?_ (pow_pos (sub_pos.mpr hvw) 3)
      have hH_ub := H_le_poly5 hv0
      have hHp_lb := poly6_le_neg_HDeriv hv0
      have hcert := cert_case1_bernstein hv0 hv25
      have hgap : (0 : ℝ) < 6889 / 400 - v := by linarith
      have h2 := mul_le_mul_of_nonneg_left (by linarith :
        (1 / 3) * v ^ 0 + (-4 / 45) * v ^ 1 + (1 / 105) * v ^ 2 +
        (-8 / 14175) * v ^ 3 + (2 / 93555) * v ^ 4 + (-8 / 14189175) * v ^ 5 - 1 / 140 ≤
        -HDeriv v - 1 / 140) hgap.le
      have hcert' : 0 < (6889 / 400 - v) * (-HDeriv v - 1 / 140) - 2 * H v := by linarith
      have hH_nn : 0 ≤ H v := H_nonneg hv0
      have hneg_pos : 0 < -HDeriv v - 1 / 140 := by
        by_contra hle; push Not at hle
        have := mul_nonpos_of_nonneg_of_nonpos hgap.le hle
        linarith
      have hmul : (6889 / 400 - v) * (-HDeriv v - 1 / 140) ≤ (w - v) * (-HDeriv v - 1 / 140) :=
        mul_le_mul_of_nonneg_right (by linarith) hneg_pos.le
      have hstep : (w - v) * (HDeriv v + HDeriv w) ≤ (w - v) * (HDeriv v + 1 / 140) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_pos.mpr hvw).le
      linarith
  exact hanti (Set.left_mem_Icc.mpr ha12.le) (Set.right_mem_Icc.mpr ha12.le) ha12

/-! ### 4. Subcase 2A: Pure Algebraic Direct-Difference Criterion -/

private theorem H_sq_le_div_sq {x s : ℝ} (hx : 0 < x) (hs_nn : 0 ≤ s)
    (hsin : |Real.sin x| ≤ s) :
    H (x ^ 2) ≤ s ^ 2 / x ^ 2 := by
  have hH : H (x ^ 2) = (Real.sin x) ^ 2 / x ^ 2 := by
    simp only [H, (sq_pos_of_pos hx).ne', ↓reduceIte, Real.sqrt_sq hx.le]
    have htrig : 1 - Real.cos (2 * x) = 2 * (Real.sin x) ^ 2 := by
      have := Real.cos_two_mul x
      have := Real.sin_sq_add_cos_sq x
      linarith
    rw [htrig]; ring
  rw [hH]
  have hsq : (Real.sin x) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs (Real.sin x)]
    exact sq_le_sq' (by linarith [abs_nonneg (Real.sin x)]) hsin
  exact div_le_div_of_nonneg_right hsq (sq_nonneg x)

private theorem abs_sin_le_abs_sub_pi (x : ℝ) : |Real.sin x| ≤ |x - Real.pi| := by
  have h : |Real.sin x| = |Real.sin (x - Real.pi)| := by rw [Real.sin_sub_pi, abs_neg]
  rw [h]; exact Real.abs_sin_le_abs

private theorem abs_sin_le_abs_sub_two_pi (x : ℝ) : |Real.sin x| ≤ |x - 2 * Real.pi| := by
  have h : |Real.sin x| = |Real.sin (x - 2 * Real.pi)| := by rw [Real.sin_sub_two_pi]
  rw [h]; exact Real.abs_sin_le_abs

private theorem Hww_lt_of_direct {u x1 x s : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hs_nn : 0 ≤ s) (hsin : |Real.sin x1| ≤ s)
    (hpos : 0 < (4052 / 10000 : ℝ) -
      (s ^ 2 / x1 ^ 2) / (1 - x1 ^ 2 / x ^ 2) ^ 2 -
      (x1 ^ 2 / (x ^ 2 - x1 ^ 2)) / (2 * x)) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  set w0 := u ^ 2
  set w1 := x1 ^ 2
  set w := x ^ 2
  have hx1_pos : 0 < x1 := lt_trans hu0 hu_x1
  have hx_pos : 0 < x := lt_trans hx1_pos hx1x
  have hw01 : w0 < w1 := by simp only [w0, w1]; nlinarith
  have hw1w : w1 < w := by simp only [w1, w]; nlinarith
  have hw0w : w0 < w := lt_trans hw01 hw1w
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hHu0 : (4052 / 10000 : ℝ) < H w0 := by
    have hj := four_div_pi_sq_le_H_sq hu0 hu.le
    have hpi2 : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_pos]
    have hdiv : (4052 / 10000 : ℝ) < 4 / Real.pi ^ 2 := by
      rw [div_lt_div_iff₀ (by norm_num) (sq_pos_of_pos Real.pi_pos)]
      nlinarith
    linarith
  have hHw_nn : 0 ≤ H w := H_nonneg (sq_pos_of_pos hx_pos)
  have hHw1_ub : H w1 ≤ s ^ 2 / w1 := H_sq_le_div_sq hx1_pos hs_nn hsin
  have hHw1_nn : 0 ≤ H w1 := H_nonneg (sq_pos_of_pos hx1_pos)
  have hHpw_ub : HDeriv w ≤ 1 / (2 * x ^ 3) := by
    unfold HDeriv
    rw [show Real.sqrt w = x from Real.sqrt_sq hx_pos.le]
    have hsinx : Real.sin (2 * x) ≤ 1 := Real.sin_le_one _
    have hcosx : Real.cos (2 * x) ≤ 1 := Real.cos_le_one _
    have hnum : x * Real.sin (2 * x) + Real.cos (2 * x) - 1 ≤ x := by nlinarith
    have hstep : (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) / (2 * w ^ 2) ≤ x / (2 * w ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have heq : x / (2 * w ^ 2) = 1 / (2 * x ^ 3) := by
      simp only [w]; field_simp [hx_pos.ne']
    linarith
  suffices hmul : 0 < (w - w0) ^ 2 * (Hww w0 w - Hww w1 w) by
    have hsq_pos : 0 < (w - w0) ^ 2 := sq_pos_of_pos (sub_pos.mpr hw0w)
    by_contra hle; push Not at hle
    have := mul_nonpos_of_nonneg_of_nonpos hsq_pos.le (sub_nonpos.mpr hle)
    linarith
  have hident : (w - w0) ^ 2 * (Hww w0 w - Hww w1 w) =
      H w0 + H w * ((w - w0) ^ 2 / (w - w1) ^ 2 - 1) -
      ((w - w0) / (w - w1)) ^ 2 * H w1 -
      HDeriv w * ((w1 - w0) * (w - w0) / (w - w1)) := by
    unfold Hww
    field_simp [(sub_pos.mpr hw0w).ne', (sub_pos.mpr hw1w).ne']
    ring
  rw [hident]
  have hHw_term : 0 ≤ H w * ((w - w0) ^ 2 / (w - w1) ^ 2 - 1) := by
    have hge1 : 1 ≤ (w - w0) ^ 2 / (w - w1) ^ 2 := by
      rw [one_le_div (sq_pos_of_pos (sub_pos.mpr hw1w))]
      nlinarith
    exact mul_nonneg hHw_nn (by linarith)
  have h1m_pos : 0 < 1 - w1 / w := by
    rw [sub_pos, div_lt_one (sq_pos_of_pos hx_pos)]; exact hw1w
  have hratio_le : ((w - w0) / (w - w1)) ^ 2 ≤ 1 / (1 - w1 / w) ^ 2 := by
    have heq : 1 / (1 - w1 / w) = w / (w - w1) := by
      have hw_pos : 0 < w := sq_pos_of_pos hx_pos
      have h1m_eq : 1 - w1 / w = (w - w1) / w := by field_simp [hw_pos.ne']
      rw [h1m_eq, one_div_div]
    have hr : (w - w0) / (w - w1) ≤ 1 / (1 - w1 / w) := by
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith [sq_nonneg u]) (sub_pos.mpr hw1w).le
    have hnn : 0 ≤ (w - w0) / (w - w1) := div_nonneg (sub_pos.mpr hw0w).le (sub_pos.mpr hw1w).le
    have hsq1 : ((w - w0) / (w - w1)) ^ 2 ≤ (1 / (1 - w1 / w)) ^ 2 := by nlinarith
    have hsq2 : (1 / (1 - w1 / w)) ^ 2 = 1 / (1 - w1 / w) ^ 2 := by rw [div_pow, one_pow]
    linarith
  have hterm1 : ((w - w0) / (w - w1)) ^ 2 * H w1 ≤ (s ^ 2 / w1) / (1 - w1 / w) ^ 2 := by
    have h1 := mul_le_mul hratio_le hHw1_ub hHw1_nn (by positivity)
    linarith [show 1 / (1 - w1 / w) ^ 2 * (s ^ 2 / w1) = (s ^ 2 / w1) / (1 - w1 / w) ^ 2 by ring]
  have hterm2 : HDeriv w * ((w1 - w0) * (w - w0) / (w - w1)) ≤ (w1 / (w - w1)) / (2 * x) := by
    have hfac_nn : 0 ≤ (w1 - w0) * (w - w0) / (w - w1) :=
      div_nonneg (mul_nonneg (sub_pos.mpr hw01).le (sub_pos.mpr hw0w).le) (sub_pos.mpr hw1w).le
    have hfac_le : (w1 - w0) * (w - w0) / (w - w1) ≤ w1 * w / (w - w1) := by
      refine div_le_div_of_nonneg_right ?_ (sub_pos.mpr hw1w).le
      have : 0 ≤ w0 := sq_nonneg u
      nlinarith
    have h1 : HDeriv w * ((w1 - w0) * (w - w0) / (w - w1)) ≤
        (1 / (2 * x ^ 3)) * ((w1 - w0) * (w - w0) / (w - w1)) :=
      mul_le_mul_of_nonneg_right hHpw_ub hfac_nn
    have h2 : (1 / (2 * x ^ 3)) * ((w1 - w0) * (w - w0) / (w - w1)) ≤
        (1 / (2 * x ^ 3)) * (w1 * w / (w - w1)) :=
      mul_le_mul_of_nonneg_left hfac_le (by positivity)
    have h3 : (1 / (2 * x ^ 3)) * (w1 * w / (w - w1)) = (w1 / (w - w1)) / (2 * x) := by
      simp only [w]; field_simp [hx_pos.ne', (sub_pos.mpr hw1w).ne']
    linarith
  linarith

private theorem direct_box_ok {u x1 x s_max a1 b1 x_lo : ℝ}
    (hu0 : 0 < u) (hu : u < Real.pi / 2) (hu_x1 : u < x1) (hx1x : x1 < x)
    (ha1 : 0 < a1) (hx1_lo : a1 ≤ x1) (hx1_hi : x1 ≤ b1) (hb1_lt : b1 < x_lo) (hx_lo : x_lo ≤ x)
    (hs_nn : 0 ≤ s_max) (hsin : |Real.sin x1| ≤ s_max)
    (hnum : (s_max ^ 2 / a1 ^ 2) / (1 - b1 ^ 2 / x_lo ^ 2) ^ 2 +
      (b1 ^ 2 / (x_lo ^ 2 - b1 ^ 2)) / (2 * x_lo) < 4052 / 10000) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := lt_of_lt_of_le ha1 hx1_lo
  have hb1_pos : 0 < b1 := lt_of_lt_of_le hx1_pos hx1_hi
  have hx_lo_pos : 0 < x_lo := lt_trans hb1_pos hb1_lt
  have hx_pos : 0 < x := lt_of_lt_of_le hx_lo_pos hx_lo
  have hr1 : s_max ^ 2 / x1 ^ 2 ≤ s_max ^ 2 / a1 ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg s_max) (sq_pos_of_pos ha1) (by nlinarith)
  have hrat : x1 ^ 2 / x ^ 2 ≤ b1 ^ 2 / x_lo ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hx_pos) (sq_pos_of_pos hx_lo_pos)]
    have h1 : x1 ^ 2 ≤ b1 ^ 2 := by nlinarith
    have h2 : x_lo ^ 2 ≤ x ^ 2 := by nlinarith
    nlinarith
  have h1m_pos : 0 < 1 - b1 ^ 2 / x_lo ^ 2 := by
    rw [sub_pos, div_lt_one (sq_pos_of_pos hx_lo_pos)]; nlinarith
  have h1m_le : 1 - b1 ^ 2 / x_lo ^ 2 ≤ 1 - x1 ^ 2 / x ^ 2 := by linarith
  have ht1 : (s_max ^ 2 / x1 ^ 2) / (1 - x1 ^ 2 / x ^ 2) ^ 2 ≤
      (s_max ^ 2 / a1 ^ 2) / (1 - b1 ^ 2 / x_lo ^ 2) ^ 2 := by
    have hsq : (1 - b1 ^ 2 / x_lo ^ 2) ^ 2 ≤ (1 - x1 ^ 2 / x ^ 2) ^ 2 := by nlinarith
    exact le_trans (div_le_div_of_nonneg_right hr1 (by positivity))
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos h1m_pos) hsq)
  have hdiff_lo : 0 < x_lo ^ 2 - b1 ^ 2 := by nlinarith
  have ht2 : (x1 ^ 2 / (x ^ 2 - x1 ^ 2)) / (2 * x) ≤
      (b1 ^ 2 / (x_lo ^ 2 - b1 ^ 2)) / (2 * x_lo) := by
    have hfrac : x1 ^ 2 / (x ^ 2 - x1 ^ 2) ≤ b1 ^ 2 / (x_lo ^ 2 - b1 ^ 2) := by
      rw [div_le_div_iff₀ (by nlinarith) hdiff_lo]
      have h1 : x1 ^ 2 ≤ b1 ^ 2 := by nlinarith
      have h2 : x_lo ^ 2 ≤ x ^ 2 := by nlinarith
      nlinarith
    exact le_trans (div_le_div_of_nonneg_right hfrac (by positivity))
      (div_le_div_of_nonneg_left (div_nonneg (sq_nonneg b1) hdiff_lo.le) (by positivity) (by linarith))
  exact Hww_lt_of_direct hu0 hu hu_x1 hx1x hs_nn hsin (by linarith)

/-! ### 5. Exact Global Lower Bound `L(x)` on `x⁴ Hww ((π/2)²) (x²)` -/

private theorem sin_shift_3pi (z : ℝ) : Real.sin z = -Real.sin (z - 3 * Real.pi) := by
  have h : Real.sin ((z - 3 * Real.pi) + Real.pi + 2 * Real.pi) = -Real.sin (z - 3 * Real.pi) := by
    rw [Real.sin_add_two_pi, Real.sin_add_pi]
  rwa [show (z - 3 * Real.pi) + Real.pi + 2 * Real.pi = z by ring] at h

private theorem cos_shift_3pi (z : ℝ) : Real.cos z = -Real.cos (z - 3 * Real.pi) := by
  have h : Real.cos ((z - 3 * Real.pi) + Real.pi + 2 * Real.pi) = -Real.cos (z - 3 * Real.pi) := by
    rw [Real.cos_add_two_pi, Real.cos_add_pi]
  rwa [show (z - 3 * Real.pi) + Real.pi + 2 * Real.pi = z by ring] at h

private theorem sin_shift_4pi (z : ℝ) : Real.sin z = Real.sin (z - 4 * Real.pi) := by
  have h : Real.sin ((z - 4 * Real.pi) + 2 * Real.pi + 2 * Real.pi) = Real.sin (z - 4 * Real.pi) := by
    rw [Real.sin_add_two_pi, Real.sin_add_two_pi]
  rwa [show (z - 4 * Real.pi) + 2 * Real.pi + 2 * Real.pi = z by ring] at h

private theorem cos_shift_4pi (z : ℝ) : Real.cos z = Real.cos (z - 4 * Real.pi) := by
  have h : Real.cos ((z - 4 * Real.pi) + 2 * Real.pi + 2 * Real.pi) = Real.cos (z - 4 * Real.pi) := by
    rw [Real.cos_add_two_pi, Real.cos_add_two_pi]
  rwa [show (z - 4 * Real.pi) + 2 * Real.pi + 2 * Real.pi = z by ring] at h

private theorem sin_shift_5pi (z : ℝ) : Real.sin z = -Real.sin (z - 5 * Real.pi) := by
  have h : Real.sin ((z - 5 * Real.pi) + Real.pi + 2 * Real.pi + 2 * Real.pi) = -Real.sin (z - 5 * Real.pi) := by
    rw [Real.sin_add_two_pi, Real.sin_add_two_pi, Real.sin_add_pi]
  rwa [show (z - 5 * Real.pi) + Real.pi + 2 * Real.pi + 2 * Real.pi = z by ring] at h

private theorem cos_shift_5pi (z : ℝ) : Real.cos z = -Real.cos (z - 5 * Real.pi) := by
  have h : Real.cos ((z - 5 * Real.pi) + Real.pi + 2 * Real.pi + 2 * Real.pi) = -Real.cos (z - 5 * Real.pi) := by
    rw [Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_pi]
  rwa [show (z - 5 * Real.pi) + Real.pi + 2 * Real.pi + 2 * Real.pi = z by ring] at h

private theorem Hww_pi_half_decomp {x : ℝ} (hx : 4 ≤ x) :
    let a := (Real.pi / 2) ^ 2
    let w := x ^ 2
    (w - a) ^ 2 * Hww a w =
      (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
      ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
      (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) := by
  intro a w
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := sq_pos_of_pos hx0
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have ha0 : 0 < a := sq_pos_of_pos (div_pos Real.pi_pos two_pos)
  have hwa : a < w := by simp only [a, w]; nlinarith [Real.pi_pos]
  have hHa : H a = 4 / Real.pi ^ 2 := by
    simp only [H, ha0.ne', ↓reduceIte, a]
    rw [Real.sqrt_sq (div_pos Real.pi_pos two_pos).le]
    have : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [this, Real.cos_pi]
    field_simp [Real.pi_pos.ne']; ring
  have hHw : H w = (1 - Real.cos (2 * x)) / (2 * w) := by
    simp only [H, hw0.ne', ↓reduceIte, w, Real.sqrt_sq hx0.le]
  have hHpw : HDeriv w = (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) / (2 * w ^ 2) := by
    simp only [HDeriv, w, Real.sqrt_sq hx0.le]
  unfold Hww
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 (sub_pos.mpr hwa).ne'), hHa, hHw, hHpw]
  field_simp [hw0.ne']
  ring

private theorem lower_bound_33_tail_poly {a t : ℝ} (ha_gt : 2467 / 1000 < a) (ha_lt : a < 2468 / 1000)
    (ht : 0 < t) :
    (33 / 100 : ℝ) * ((t + 5) ^ 2 - a) ^ 2 <
      4052 / 10000 * (t + 5) ^ 4 - (t + 5) ^ 2 + a / 2 -
      (t + 5) * ((t + 5) ^ 2 - a + 21 / 10) / 2 := by
  have hcoeff :
      (4052 / 10000 * (t + 5) ^ 4 - (t + 5) ^ 2 + a / 2 - (t + 5) * ((t + 5) ^ 2 - a + 21 / 10) / 2) -
      (33 / 100) * ((t + 5) ^ 2 - a) ^ 2 =
      47 / 625 * t ^ 4 + 251 / 250 * t ^ 3 +
      (139 / 50 + 33 / 50 * a) * t ^ 2 +
      (-219 / 20 + 71 / 10 * a) * t +
      (-183 / 4 + 39 / 2 * a - 33 / 100 * a ^ 2) := by ring
  have ha0 : 0 < a := by linarith only [ha_gt]
  have ht1 : 0 < -219 / 20 + 71 / 10 * a := by linarith only [ha_gt]
  have hconst : 0 < -183 / 4 + 39 / 2 * a - 33 / 100 * a ^ 2 := by nlinarith only [ha_gt, ha_lt]
  have hpos_all : 0 < 47 / 625 * t ^ 4 + 251 / 250 * t ^ 3 +
      (139 / 50 + 33 / 50 * a) * t ^ 2 +
      (-219 / 20 + 71 / 10 * a) * t +
      (-183 / 4 + 39 / 2 * a - 33 / 100 * a ^ 2) := by positivity
  linarith only [hcoeff, hpos_all]

/-- Global lower bound: `33/100 < x⁴ Hww ((π/2)²) (x²)` for ALL `x ≥ 83/20`. -/
private theorem lower_bound_33 {x : ℝ} (hx : 83 / 20 ≤ x) :
    (33 / 100 : ℝ) < x ^ 4 * Hww ((Real.pi / 2) ^ 2) (x ^ 2) := by
  set a := (Real.pi / 2) ^ 2
  set w := x ^ 2
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := sq_pos_of_pos hx0
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have ha_gt : (2467 / 1000 : ℝ) < a := by simp only [a]; nlinarith only [hpi_gt]
  have ha_lt : a < 2468 / 1000 := by simp only [a]; nlinarith only [hpi_lt, Real.pi_pos]
  have h4pi : (4052 / 10000 : ℝ) < 4 / Real.pi ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (sq_pos_of_pos Real.pi_pos)]
    nlinarith only [hpi_lt, Real.pi_pos]
  have hwa : a < w := by simp only [w]; nlinarith only [hx, ha_lt]
  have hwa_pos : 0 < w - a := sub_pos.mpr hwa
  have hdecomp := Hww_pi_half_decomp (by linarith : (4 : ℝ) ≤ x)
  change (w - a) ^ 2 * Hww a w =
    (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
    ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
    (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) at hdecomp
  suffices hgoal : (33 / 100 : ℝ) * (w - a) ^ 2 < w ^ 2 * ((w - a) ^ 2 * Hww a w) by
    have heq : w ^ 2 * ((w - a) ^ 2 * Hww a w) = (w - a) ^ 2 * (x ^ 4 * Hww a w) := by
      simp only [w]; ring
    rw [heq] at hgoal
    have hsq : 0 < (w - a) ^ 2 := sq_pos_of_pos hwa_pos
    nlinarith only [hgoal, hsq]
  rw [hdecomp]
  have hcc_pos : 0 < (2 * w - a) / (2 * w ^ 2) := div_pos (by linarith only [hwa, ha_gt]) (by positivity)
  have hcs_pos : 0 < x * (w - a) / (2 * w ^ 2) := div_pos (mul_pos hx0 hwa_pos) (by positivity)
  by_cases hx1 : x ≤ 3 * Real.pi / 2
  · have hsin_nn : 0 ≤ Real.sin (2 * x) := by
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith only [hx, hpi_lt]) (by linarith only [hx1])
    have hcos_lb : -1 ≤ Real.cos (2 * x) := Real.neg_one_le_cos _
    have hc := mul_le_mul_of_nonneg_left hcos_lb hcc_pos.le
    have hs := mul_nonneg hcs_pos.le hsin_nn
    have halg : (4052 / 10000 : ℝ) - 1 / w + a / (2 * w ^ 2) - (2 * w - a) / (2 * w ^ 2) =
        4052 / 10000 - 2 / w + a / w ^ 2 := by field_simp [hw0.ne']; ring
    have hlin : (4052 / 10000 : ℝ) - 2 / w + a / w ^ 2 <
        (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
        ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
        (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) := by linarith only [h4pi, hc, hs, halg]
    have heq : w ^ 2 * (4052 / 10000 - 2 / w + a / w ^ 2) = 4052 / 10000 * w ^ 2 - 2 * w + a := by
      field_simp [hw0.ne']
    have hw17 : (172 / 10 : ℝ) ≤ w := by simp only [w]; nlinarith only [hx]
    have hpoly : (33 / 100 : ℝ) * (w - a) ^ 2 < w ^ 2 * (4052 / 10000 - 2 / w + a / w ^ 2) := by
      rw [heq]; nlinarith only [hw17, ha_gt, ha_lt]
    have hmul := mul_lt_mul_of_pos_left hlin (sq_pos_of_pos hw0)
    linarith only [hpoly, hmul]
  · push Not at hx1
    by_cases hx2 : x ≤ 5
    · have hsin_lb : -(58 / 100 : ℝ) ≤ Real.sin (2 * x) := by
        rw [sin_shift_3pi (2 * x)]
        have h1 : Real.sin (2 * x - 3 * Real.pi) ≤ 2 * x - 3 * Real.pi :=
          Real.sin_le (by linarith only [hx1])
        linarith only [h1, hx2, hpi_gt]
      have hcos_lb : -1 ≤ Real.cos (2 * x) := Real.neg_one_le_cos _
      have hc := mul_le_mul_of_nonneg_left hcos_lb hcc_pos.le
      have hs := mul_le_mul_of_nonneg_left hsin_lb hcs_pos.le
      have halg : (4052 / 10000 : ℝ) - 1 / w + a / (2 * w ^ 2) - (2 * w - a) / (2 * w ^ 2) =
          4052 / 10000 - 2 / w + a / w ^ 2 := by field_simp [hw0.ne']; ring
      have hlin : (4052 / 10000 : ℝ) - 2 / w + a / w ^ 2 - (58 / 100) * (x * (w - a) / (2 * w ^ 2)) <
          (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
          ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
          (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) := by linarith only [h4pi, hc, hs, halg]
      have heq : w ^ 2 * (4052 / 10000 - 2 / w + a / w ^ 2 - (58 / 100) * (x * (w - a) / (2 * w ^ 2))) =
          4052 / 10000 * w ^ 2 - 2 * w + a - (29 / 100) * x * (w - a) := by
        field_simp [hw0.ne']; ring
      have hx_gt47 : (47 / 10 : ℝ) < x := by linarith only [hx1, hpi_gt]
      have hw_gt22 : (2209 / 100 : ℝ) < w := by simp only [w]; nlinarith only [hx_gt47]
      have hxw_le : x * (w - a) ≤ 5 * (w - a) := mul_le_mul_of_nonneg_right hx2 hwa_pos.le
      have hpoly : (33 / 100 : ℝ) * (w - a) ^ 2 <
          w ^ 2 * (4052 / 10000 - 2 / w + a / w ^ 2 - (58 / 100) * (x * (w - a) / (2 * w ^ 2))) := by
        rw [heq]; nlinarith only [hw_gt22, ha_gt, ha_lt, hxw_le]
      have hmul := mul_lt_mul_of_pos_left hlin (sq_pos_of_pos hw0)
      linarith only [hpoly, hmul]
    · push Not at hx2
      have hcs_lb : -((w - a + 21 / 10) / (2 * w * x)) ≤
          ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
          (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) := by
        have hcs : ((2 * w - a) * Real.cos (2 * x) + x * (w - a) * Real.sin (2 * x)) ^ 2 ≤
            (2 * w - a) ^ 2 + w * (w - a) ^ 2 := by
          have hsc := Real.sin_sq_add_cos_sq (2 * x)
          have hxw : x ^ 2 = w := rfl
          nlinarith only [hsc, hxw, sq_nonneg ((2 * w - a) * Real.sin (2 * x) - x * (w - a) * Real.cos (2 * x))]
        have hw25 : (25 : ℝ) < w := by simp only [w]; nlinarith only [hx2]
        have hdom : (2 * w - a) ^ 2 + w * (w - a) ^ 2 ≤ w * (w - a + 21 / 10) ^ 2 := by
          have hdiff : w * (w - a + 21 / 10) ^ 2 - ((2 * w - a) ^ 2 + w * (w - a) ^ 2) =
              (2 / 10) * w ^ 2 + (441 / 100 - 2 / 10 * a) * w - a ^ 2 := by ring
          nlinarith only [hdiff, hw25, ha_gt, ha_lt]
        have hstep : ((2 * w - a) * Real.cos (2 * x) + x * (w - a) * Real.sin (2 * x)) ^ 2 ≤
            w * (w - a + 21 / 10) ^ 2 := le_trans hcs hdom
        have hdiv := div_le_div_of_nonneg_right hstep (by positivity : (0 : ℝ) ≤ (2 * w ^ 2) ^ 2)
        have hlhs : (((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
            (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x)) ^ 2 =
            ((2 * w - a) * Real.cos (2 * x) + x * (w - a) * Real.sin (2 * x)) ^ 2 / (2 * w ^ 2) ^ 2 := by ring
        have hrhs : w * (w - a + 21 / 10) ^ 2 / (2 * w ^ 2) ^ 2 =
            ((w - a + 21 / 10) / (2 * w * x)) ^ 2 := by
          simp only [w]; field_simp [hx0.ne']
        have hR_nn : 0 ≤ (w - a + 21 / 10) / (2 * w * x) := by positivity
        nlinarith only [hdiv, hlhs, hrhs, hR_nn]
      have heq : w ^ 2 * (4052 / 10000 - 1 / w + a / (2 * w ^ 2) - (w - a + 21 / 10) / (2 * w * x)) =
          4052 / 10000 * w ^ 2 - w + a / 2 - x * (w - a + 21 / 10) / 2 := by
        simp only [w]; field_simp [hx0.ne']
      have hpoly : (33 / 100 : ℝ) * (w - a) ^ 2 <
          w ^ 2 * (4052 / 10000 - 1 / w + a / (2 * w ^ 2) - (w - a + 21 / 10) / (2 * w * x)) := by
        rw [heq]
        have htp := lower_bound_33_tail_poly ha_gt ha_lt (by linarith only [hx2] : 0 < x - 5)
        have hx5 : (x - 5) + 5 = x := by ring
        rw [hx5] at htp
        have hw_def : x ^ 2 = w := rfl
        have hw4 : x ^ 4 = w ^ 2 := by simp only [w]; ring
        linarith only [htp, hw_def, hw4]
      have hmul := mul_lt_mul_of_pos_left (by linarith only [h4pi, hcs_lb] :
        (4052 / 10000 : ℝ) - 1 / w + a / (2 * w ^ 2) - (w - a + 21 / 10) / (2 * w * x) <
        (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
        ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
        (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x)) (sq_pos_of_pos hw0)
      linarith only [hpoly, hmul]

/-- Boosted lower bound on `[6, 27/4]`: `19/50 < x⁴ Hww ((π/2)²) (x²)`. -/
private theorem lower_bound_38 {x : ℝ} (hx_lo : 6 ≤ x) (hx_hi : x ≤ 27 / 4) :
    (19 / 50 : ℝ) < x ^ 4 * Hww ((Real.pi / 2) ^ 2) (x ^ 2) := by
  set a := (Real.pi / 2) ^ 2
  set w := x ^ 2
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := sq_pos_of_pos hx0
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have ha_gt : (2467 / 1000 : ℝ) < a := by simp only [a]; nlinarith only [hpi_gt]
  have ha_lt : a < 2468 / 1000 := by simp only [a]; nlinarith only [hpi_lt, Real.pi_pos]
  have h4pi : (4052 / 10000 : ℝ) < 4 / Real.pi ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (sq_pos_of_pos Real.pi_pos)]
    nlinarith only [hpi_lt, Real.pi_pos]
  have hwa_pos : 0 < w - a := by simp only [w]; nlinarith only [hx_lo, ha_lt]
  have hdecomp := Hww_pi_half_decomp (by linarith : (4 : ℝ) ≤ x)
  change (w - a) ^ 2 * Hww a w =
    (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
    ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
    (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) at hdecomp
  suffices hgoal : (19 / 50 : ℝ) * (w - a) ^ 2 < w ^ 2 * ((w - a) ^ 2 * Hww a w) by
    have heq : w ^ 2 * ((w - a) ^ 2 * Hww a w) = (w - a) ^ 2 * (x ^ 4 * Hww a w) := by
      simp only [w]; ring
    rw [heq] at hgoal
    have hsq : 0 < (w - a) ^ 2 := sq_pos_of_pos hwa_pos
    nlinarith only [hgoal, hsq]
  rw [hdecomp]
  have hcc_pos : 0 < (2 * w - a) / (2 * w ^ 2) := div_pos (by linarith only [hwa_pos, ha_gt]) (by positivity)
  have hcs_pos : 0 < x * (w - a) / (2 * w ^ 2) := div_pos (mul_pos hx0 hwa_pos) (by positivity)
  have hcos_lb : (55 / 100 : ℝ) ≤ Real.cos (2 * x) := by
    rw [cos_shift_4pi (2 * x)]
    have htb := one_sub_cos_le_sq_div_two (2 * x - 4 * Real.pi)
    have hsq : (2 * x - 4 * Real.pi) ^ 2 / 2 ≤ 45 / 100 := by nlinarith only [hx_lo, hx_hi, hpi_gt, hpi_lt]
    linarith only [htb, hsq]
  have hsin_lb : -(57 / 100 : ℝ) ≤ Real.sin (2 * x) := by
    rw [sin_shift_4pi (2 * x)]
    by_cases hsign : 0 ≤ 2 * x - 4 * Real.pi
    · have : 0 ≤ Real.sin (2 * x - 4 * Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hsign (by linarith only [hx_hi, hpi_gt])
      linarith only [this]
    · push Not at hsign
      have hneg : Real.sin (2 * x - 4 * Real.pi) = -Real.sin (4 * Real.pi - 2 * x) := by
        rw [← Real.sin_neg]; congr 1; ring
      rw [hneg]
      have hle := Real.sin_le (by linarith only [hsign] : 0 ≤ 4 * Real.pi - 2 * x)
      linarith only [hle, hx_lo, hpi_lt]
  have hc := mul_le_mul_of_nonneg_left hcos_lb hcc_pos.le
  have hs := mul_le_mul_of_nonneg_left hsin_lb hcs_pos.le
  have hlin : (4052 / 10000 : ℝ) - 1 / w + a / (2 * w ^ 2) +
      (55 / 100) * ((2 * w - a) / (2 * w ^ 2)) - (57 / 100) * (x * (w - a) / (2 * w ^ 2)) <
      (4 / Real.pi ^ 2 - 1 / w + a / (2 * w ^ 2)) +
      ((2 * w - a) / (2 * w ^ 2)) * Real.cos (2 * x) +
      (x * (w - a) / (2 * w ^ 2)) * Real.sin (2 * x) := by linarith only [h4pi, hc, hs]
  have heq : w ^ 2 * (4052 / 10000 - 1 / w + a / (2 * w ^ 2) +
      (55 / 100) * ((2 * w - a) / (2 * w ^ 2)) - (57 / 100) * (x * (w - a) / (2 * w ^ 2))) =
      4052 / 10000 * w ^ 2 - 45 / 100 * w + 9 / 40 * a - 57 / 200 * x * (w - a) := by
    field_simp [hw0.ne']; ring
  have hw36 : (36 : ℝ) ≤ w := by simp only [w]; nlinarith only [hx_lo]
  have hxw : x * (w - a) ≤ (27 / 4) * (w - a) := mul_le_mul_of_nonneg_right hx_hi hwa_pos.le
  have hpoly : (19 / 50 : ℝ) * (w - a) ^ 2 <
      w ^ 2 * (4052 / 10000 - 1 / w + a / (2 * w ^ 2) +
        (55 / 100) * ((2 * w - a) / (2 * w ^ 2)) - (57 / 100) * (x * (w - a) / (2 * w ^ 2))) := by
    rw [heq]; nlinarith only [hw36, ha_gt, ha_lt, hxw]
  have hmul := mul_lt_mul_of_pos_left hlin (sq_pos_of_pos hw0)
  linarith only [hpoly, hmul]

/-! ### 6. Piecewise Majorant `HDeriv2 v ≤ M(v)` via Monotonicity & Global Cauchy-Schwarz -/

private theorem HDeriv2_le_global_cs {v : ℝ} (hv : 7 / 3 ≤ v) :
    HDeriv2 v ≤ 1 / (2 * v ^ 2) + 7 / (4 * v ^ 3) := by
  have hv0 : 0 < v := by linarith
  set x := Real.sqrt v
  have hxv : x ^ 2 = v := Real.sq_sqrt hv0.le
  unfold HDeriv2
  change ((2 * v - 4) * Real.cos (2 * x) - 5 * x * Real.sin (2 * x) + 4) / (4 * v ^ 3) ≤
    1 / (2 * v ^ 2) + 7 / (4 * v ^ 3)
  have hcs : ((2 * v - 4) * Real.cos (2 * x) - 5 * x * Real.sin (2 * x)) ^ 2 ≤
      (2 * v - 4) ^ 2 + 25 * x ^ 2 := by
    have hsc := Real.sin_sq_add_cos_sq (2 * x)
    nlinarith only [hsc, sq_nonneg ((2 * v - 4) * Real.sin (2 * x) + 5 * x * Real.cos (2 * x))]
  have hdom : (2 * v - 4) ^ 2 + 25 * v ≤ (2 * v + 3) ^ 2 := by nlinarith only [hv]
  have hlin : (2 * v - 4) * Real.cos (2 * x) - 5 * x * Real.sin (2 * x) ≤ 2 * v + 3 := by
    rw [hxv] at hcs; nlinarith only [hcs, hdom, hv]
  have hstep := div_le_div_of_nonneg_right (by linarith only [hlin] :
    (2 * v - 4) * Real.cos (2 * x) - 5 * x * Real.sin (2 * x) + 4 ≤ 2 * v + 7)
    (by positivity : (0 : ℝ) ≤ 4 * v ^ 3)
  have heq : (2 * v + 7) / (4 * v ^ 3) = 1 / (2 * v ^ 2) + 7 / (4 * v ^ 3) := by
    field_simp [hv0.ne']; ring
  linarith only [hstep, heq]

private noncomputable def fHpp (x : ℝ) : ℝ :=
  (2 - 4 / x ^ 2) * Real.cos (2 * x) - (5 / x) * Real.sin (2 * x) + 4 / x ^ 2

private theorem HDeriv2_eq_fHpp {v : ℝ} (hv : 0 < v) :
    HDeriv2 v = fHpp (Real.sqrt v) / (4 * v ^ 2) := by
  set x := Real.sqrt v
  have hx0 : 0 < x := Real.sqrt_pos.mpr hv
  have hxv : x ^ 2 = v := Real.sq_sqrt hv.le
  unfold HDeriv2 fHpp
  rw [← hxv, Real.sqrt_sq hx0.le]
  field_simp [hx0.ne']

private theorem hasDerivAt_inv_real {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
  have : (fun t : ℝ => 1 / t) = fun t => t⁻¹ := by funext t; exact one_div t
  rw [this]
  refine (hasDerivAt_inv hx).congr_deriv ?_
  ring

private theorem hasDerivAt_inv_sq_real {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-2 / x ^ 3) x := by
  have : (fun t : ℝ => 1 / t ^ 2) = fun t => (t ^ 2)⁻¹ := by funext t; exact one_div (t ^ 2)
  rw [this]
  refine ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx)).congr_deriv ?_
  field_simp [hx]; ring

private theorem hasDerivAt_fHpp {x : ℝ} (hx : 0 < x) :
    HasDerivAt fHpp
      ((-4 + 13 / x ^ 2) * Real.sin (2 * x) - (10 / x - 8 / x ^ 3) * Real.cos (2 * x) - 8 / x ^ 3) x := by
  have hxne : x ≠ 0 := hx.ne'
  have h2x : HasDerivAt (fun t : ℝ => 2 * t) (2 * 1) x := (hasDerivAt_id' x).const_mul 2
  have hcos := (Real.hasDerivAt_cos (2 * x)).comp x h2x
  have hsin := (Real.hasDerivAt_sin (2 * x)).comp x h2x
  have hinv := hasDerivAt_inv_real hxne
  have hinv2 := hasDerivAt_inv_sq_real hxne
  have hc1 : HasDerivAt (fun t : ℝ => 2 - 4 / t ^ 2) (0 - 4 * (-2 / x ^ 3)) x := by
    have : (fun t : ℝ => 2 - 4 / t ^ 2) = fun t => 2 - 4 * (1 / t ^ 2) := by funext t; ring
    rw [this]; exact (hasDerivAt_const x (2 : ℝ)).fun_sub (hinv2.const_mul 4)
  have hc2 : HasDerivAt (fun t : ℝ => 5 / t) (5 * (-1 / x ^ 2)) x := by
    have : (fun t : ℝ => 5 / t) = fun t => 5 * (1 / t) := by funext t; ring
    rw [this]; exact hinv.const_mul 5
  have hc3 : HasDerivAt (fun t : ℝ => 4 / t ^ 2) (4 * (-2 / x ^ 3)) x := by
    have : (fun t : ℝ => 4 / t ^ 2) = fun t => 4 * (1 / t ^ 2) := by funext t; ring
    rw [this]; exact hinv2.const_mul 4
  have htot := ((hc1.fun_mul hcos).fun_sub (hc2.fun_mul hsin)).fun_add hc3
  refine htot.congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp [hxne]; ring

private theorem cos_ub_ord4 {y : ℝ} (hy : 0 ≤ y) :
    Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 + y ^ 8 / 40320 :=
  taylorCos5_ub hy

private theorem cos_lb_ord3 {y : ℝ} (hy : 0 ≤ y) :
    1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720 ≤ Real.cos y := by
  have h := (taylor_trig_bounds 1).2.2.1 y hy
  simp only [taylorCos, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Nat.factorial] at h
  norm_num at h; linarith

private theorem sin_lb_ord4 {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 ≤ Real.sin y := by
  have h := (taylor_trig_bounds 1).2.2.2 y hy
  simp only [taylorSin, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Nat.factorial] at h
  norm_num at h; linarith

private theorem sin_ub_ord3 {y : ℝ} (hy : 0 ≤ y) :
    Real.sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 := by
  have h := (taylor_trig_bounds 1).2.1 y hy
  simp only [taylorSin, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Nat.factorial] at h
  norm_num at h; linarith

private theorem cos_antitone_Icc {y1 y2 : ℝ} (h0 : 0 ≤ y1) (h12 : y1 ≤ y2) (h2 : y2 ≤ Real.pi) :
    Real.cos y2 ≤ Real.cos y1 :=
  Real.strictAntiOn_cos.antitoneOn ⟨h0, le_trans h12 h2⟩ ⟨le_trans h0 h12, h2⟩ h12

private theorem sin_monotone_Icc {y1 y2 : ℝ} (h0 : -(Real.pi / 2) ≤ y1) (h12 : y1 ≤ y2)
    (h2 : y2 ≤ Real.pi / 2) :
    Real.sin y1 ≤ Real.sin y2 :=
  Real.strictMonoOn_sin.monotoneOn ⟨h0, le_trans h12 h2⟩ ⟨le_trans h0 h12, h2⟩ h12

private theorem fHpp_at_340 : fHpp (17 / 5) ≤ 7 / 5 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 2 * (17 / 5 : ℝ) - 2 * Real.pi
  have hy_lo : (323 / 625 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 517 / 1000 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (17 / 5 : ℝ)) ≤ 870 / 1000 := by
    rw [← Real.cos_sub_two_pi]
    change Real.cos y ≤ 870 / 1000
    have h1 := cos_antitone_Icc (by norm_num) hy_lo (by linarith)
    have h2 := cos_ub_ord4 (by norm_num : (0 : ℝ) ≤ 323 / 625)
    norm_num at h2; linarith
  have hsin : (493 / 1000 : ℝ) ≤ Real.sin (2 * (17 / 5 : ℝ)) := by
    rw [← Real.sin_sub_two_pi]
    change 493 / 1000 ≤ Real.sin y
    have h1 := sin_monotone_Icc (by linarith) hy_lo (by linarith)
    have h2 := sin_lb_ord4 (by norm_num : (0 : ℝ) ≤ 323 / 625)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_at_366 : fHpp (183 / 50) ≤ 0 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 2 * (183 / 50 : ℝ) - 2 * Real.pi
  have hy_lo : (648 / 625 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 1037 / 1000 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (183 / 50 : ℝ)) ≤ 5092 / 10000 := by
    rw [← Real.cos_sub_two_pi]
    change Real.cos y ≤ 5092 / 10000
    have h1 := cos_antitone_Icc (by norm_num) hy_lo (by linarith)
    have h2 := cos_ub_ord4 (by norm_num : (0 : ℝ) ≤ 648 / 625)
    norm_num at h2; linarith
  have hsin : (8605 / 10000 : ℝ) ≤ Real.sin (2 * (183 / 50 : ℝ)) := by
    rw [← Real.sin_sub_two_pi]
    change 8605 / 10000 ≤ Real.sin y
    have h1 := sin_monotone_Icc (by linarith) hy_lo (by linarith)
    have h2 := sin_lb_ord4 (by norm_num : (0 : ℝ) ≤ 648 / 625)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_at_522 : fHpp (261 / 50) ≤ 0 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 2 * (261 / 50 : ℝ) - 3 * Real.pi
  have hy_lo : (10152 / 10000 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 10153 / 10000 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (261 / 50 : ℝ)) ≤ -(5270 / 10000) := by
    rw [cos_shift_3pi]
    change -Real.cos y ≤ -(5270 / 10000)
    have h1 := cos_antitone_Icc (by linarith) hy_hi (by linarith)
    have h2 := cos_lb_ord3 (by norm_num : (0 : ℝ) ≤ 10153 / 10000)
    norm_num at h2; linarith
  have hsin : -(8505 / 10000 : ℝ) ≤ Real.sin (2 * (261 / 50 : ℝ)) := by
    rw [sin_shift_3pi]
    change -(8505 / 10000) ≤ -Real.sin y
    have h1 := sin_monotone_Icc (by linarith) hy_hi (by linarith)
    have h2 := sin_ub_ord3 (by norm_num : (0 : ℝ) ≤ 10153 / 10000)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_at_560 : fHpp (28 / 5) ≤ 7 / 5 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 4 * Real.pi - 2 * (28 / 5 : ℝ)
  have hy_lo : (34159 / 25000 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 1708 / 1250 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (28 / 5 : ℝ)) ≤ 2033 / 10000 := by
    rw [cos_shift_4pi, ← Real.cos_neg, show -(2 * (28 / 5 : ℝ) - 4 * Real.pi) = y by simp only [y]; ring]
    have h1 := cos_antitone_Icc (by norm_num) hy_lo (by linarith)
    have h2 := cos_ub_ord4 (by norm_num : (0 : ℝ) ≤ 34159 / 25000)
    norm_num at h2; linarith
  have hsin : -(9810 / 10000 : ℝ) ≤ Real.sin (2 * (28 / 5 : ℝ)) := by
    rw [sin_shift_4pi, show 2 * (28 / 5 : ℝ) - 4 * Real.pi = -y by simp only [y]; ring, Real.sin_neg]
    have h1 := sin_monotone_Icc (by linarith) hy_hi (by linarith)
    have h2 := sin_ub_ord3 (by norm_num : (0 : ℝ) ≤ 1708 / 1250)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_at_655 : fHpp (131 / 20) ≤ 7 / 5 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 2 * (131 / 20 : ℝ) - 4 * Real.pi
  have hy_lo : (667 / 1250 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 267 / 500 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (131 / 20 : ℝ)) ≤ 8612 / 10000 := by
    rw [cos_shift_4pi]
    change Real.cos y ≤ 8612 / 10000
    have h1 := cos_antitone_Icc (by norm_num) hy_lo (by linarith)
    have h2 := cos_ub_ord4 (by norm_num : (0 : ℝ) ≤ 667 / 1250)
    norm_num at h2; linarith
  have hsin : (5080 / 10000 : ℝ) ≤ Real.sin (2 * (131 / 20 : ℝ)) := by
    rw [sin_shift_4pi]
    change 5080 / 10000 ≤ Real.sin y
    have h1 := sin_monotone_Icc (by linarith) hy_lo (by linarith)
    have h2 := sin_lb_ord4 (by norm_num : (0 : ℝ) ≤ 667 / 1250)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_at_691 : fHpp (691 / 100) ≤ 0 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 2 * (691 / 100 : ℝ) - 4 * Real.pi
  have hy_lo : (1567 / 1250 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 627 / 500 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (691 / 100 : ℝ)) ≤ 3122 / 10000 := by
    rw [cos_shift_4pi]
    change Real.cos y ≤ 3122 / 10000
    have h1 := cos_antitone_Icc (by norm_num) hy_lo (by linarith)
    have h2 := cos_ub_ord4 (by norm_num : (0 : ℝ) ≤ 1567 / 1250)
    norm_num at h2; linarith
  have hsin : (9496 / 10000 : ℝ) ≤ Real.sin (2 * (691 / 100 : ℝ)) := by
    rw [sin_shift_4pi]
    change 9496 / 10000 ≤ Real.sin y
    have h1 := sin_monotone_Icc (by linarith) hy_lo (by linarith)
    have h2 := sin_lb_ord4 (by norm_num : (0 : ℝ) ≤ 1567 / 1250)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_at_847 : fHpp (847 / 100) ≤ 0 := by
  have hpi_gt : (3.14159 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_lt : Real.pi < 3.14160 := by linarith [Real.pi_lt_d6]
  set y : ℝ := 2 * (847 / 100 : ℝ) - 5 * Real.pi
  have hy_lo : (154 / 125 : ℝ) ≤ y := by simp only [y]; linarith
  have hy_hi : y ≤ 493 / 400 := by simp only [y]; linarith
  have hcos : Real.cos (2 * (847 / 100 : ℝ)) ≤ -(3316 / 10000) := by
    rw [cos_shift_5pi]
    change -Real.cos y ≤ -(3316 / 10000)
    have h1 := cos_antitone_Icc (by linarith) hy_hi (by linarith)
    have h2 := cos_lb_ord3 (by norm_num : (0 : ℝ) ≤ 493 / 400)
    norm_num at h2; linarith
  have hsin : -(9445 / 10000 : ℝ) ≤ Real.sin (2 * (847 / 100 : ℝ)) := by
    rw [sin_shift_5pi]
    change -(9445 / 10000) ≤ -Real.sin y
    have h1 := sin_monotone_Icc (by linarith) hy_hi (by linarith)
    have h2 := sin_ub_ord3 (by norm_num : (0 : ℝ) ≤ 493 / 400)
    norm_num at h2; linarith
  unfold fHpp; nlinarith

private theorem fHpp_antitone_q1 {a b : ℝ} (ha : 3 ≤ a) (_hab : a ≤ b)
    (hsin : ∀ x ∈ Set.Icc a b, 0 ≤ Real.sin (2 * x))
    (hcos : ∀ x ∈ Set.Icc a b, 0 ≤ Real.cos (2 * x)) :
    AntitoneOn fHpp (Set.Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
  · intro x hx; exact (hasDerivAt_fHpp (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx; exact (hasDerivAt_fHpp (by linarith [(interior_subset hx).1])).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 < x := by linarith [hxm.1]
    rw [(hasDerivAt_fHpp hx0).deriv]
    have h1 : -4 + 13 / x ^ 2 ≤ 0 := by
      rw [add_comm, ← sub_eq_add_neg, sub_nonpos, div_le_iff₀ (sq_pos_of_pos hx0)]; nlinarith [hxm.1]
    have h2 : 0 ≤ 10 / x - 8 / x ^ 3 := by
      rw [sub_nonneg, div_le_div_iff₀ (pow_pos hx0 3) hx0]; nlinarith [hxm.1]
    have ht1 : (-4 + 13 / x ^ 2) * Real.sin (2 * x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (hsin x hxm)
    have ht2 : 0 ≤ (10 / x - 8 / x ^ 3) * Real.cos (2 * x) := mul_nonneg h2 (hcos x hxm)
    have ht3 : (0 : ℝ) ≤ 8 / x ^ 3 := by positivity
    linarith

private theorem fHpp_nonpos_q2 {x : ℝ} (hx : 3 ≤ x)
    (hcos : Real.cos (2 * x) ≤ 0) (hsin : 0 ≤ Real.sin (2 * x)) :
    fHpp x ≤ 0 := by
  have hx0 : 0 < x := by linarith
  unfold fHpp
  have hsc := Real.sin_sq_add_cos_sq (2 * x)
  have hsum : 1 ≤ -Real.cos (2 * x) + Real.sin (2 * x) := by
    have : 1 ≤ (-Real.cos (2 * x) + Real.sin (2 * x)) ^ 2 := by
      have : (-Real.cos (2 * x) + Real.sin (2 * x)) ^ 2 =
          (Real.cos (2 * x)) ^ 2 + (Real.sin (2 * x)) ^ 2 + 2 * (-Real.cos (2 * x)) * Real.sin (2 * x) := by ring
      nlinarith
    nlinarith
  have hc2 : 4 / x ^ 2 ≤ 5 / x := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hx0) hx0]; nlinarith
  have hmin : 4 / x ^ 2 ≤ 2 - 4 / x ^ 2 := by
    have : 4 / x ^ 2 ≤ 4 / 9 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    linarith
  have ht1 : (4 / x ^ 2) * (-Real.cos (2 * x)) ≤ (2 - 4 / x ^ 2) * (-Real.cos (2 * x)) :=
    mul_le_mul_of_nonneg_right hmin (by linarith)
  have ht2 : (4 / x ^ 2) * Real.sin (2 * x) ≤ (5 / x) * Real.sin (2 * x) :=
    mul_le_mul_of_nonneg_right hc2 hsin
  have htot : 4 / x ^ 2 ≤ (4 / x ^ 2) * (-Real.cos (2 * x) + Real.sin (2 * x)) := by
    have : (0 : ℝ) < 4 / x ^ 2 := by positivity
    nlinarith
  linarith

private theorem fHpp_monotone_q3 {a b : ℝ} (ha : 4 ≤ a) (_hab : a ≤ b)
    (hsin : ∀ x ∈ Set.Icc a b, Real.sin (2 * x) ≤ 0)
    (hcos : ∀ x ∈ Set.Icc a b, Real.cos (2 * x) ≤ 0) :
    MonotoneOn fHpp (Set.Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · intro x hx; exact (hasDerivAt_fHpp (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx; exact (hasDerivAt_fHpp (by linarith [(interior_subset hx).1])).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 < x := by linarith [hxm.1]
    rw [(hasDerivAt_fHpp hx0).deriv]
    have hsc := Real.sin_sq_add_cos_sq (2 * x)
    have hsum : 1 ≤ -Real.sin (2 * x) + (-Real.cos (2 * x)) := by
      have : 1 ≤ (-Real.sin (2 * x) - Real.cos (2 * x)) ^ 2 := by
        have : (-Real.sin (2 * x) - Real.cos (2 * x)) ^ 2 =
            (Real.sin (2 * x)) ^ 2 + (Real.cos (2 * x)) ^ 2 + 2 * (-Real.sin (2 * x)) * (-Real.cos (2 * x)) := by ring
        nlinarith [hsin x hxm, hcos x hxm]
      nlinarith [hsin x hxm, hcos x hxm]
    have h1 : 8 / x ^ 3 ≤ 4 - 13 / x ^ 2 := by
      have hx2 : 16 ≤ x ^ 2 := by nlinarith [hxm.1]
      have hx3 : 64 ≤ x ^ 3 := by nlinarith [hxm.1]
      have ha' : 8 / x ^ 3 ≤ 8 / 64 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx3
      have hb' : 13 / x ^ 2 ≤ 13 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx2
      linarith
    have h2 : 8 / x ^ 3 ≤ 10 / x - 8 / x ^ 3 := by
      have h16 : 16 / x ^ 3 ≤ 10 / x := by
        rw [div_le_div_iff₀ (pow_pos hx0 3) hx0]; nlinarith [hxm.1]
      have heq : 8 / x ^ 3 + 8 / x ^ 3 = 16 / x ^ 3 := by ring
      linarith
    have ht1 : (8 / x ^ 3) * (-Real.sin (2 * x)) ≤ (4 - 13 / x ^ 2) * (-Real.sin (2 * x)) :=
      mul_le_mul_of_nonneg_right h1 (by linarith [hsin x hxm])
    have ht2 : (8 / x ^ 3) * (-Real.cos (2 * x)) ≤ (10 / x - 8 / x ^ 3) * (-Real.cos (2 * x)) :=
      mul_le_mul_of_nonneg_right h2 (by linarith [hcos x hxm])
    have htot : 8 / x ^ 3 ≤ (8 / x ^ 3) * (-Real.sin (2 * x) + (-Real.cos (2 * x))) := by
      have : (0 : ℝ) < 8 / x ^ 3 := by positivity
      nlinarith
    linarith

private theorem HDeriv2_Z0 {v : ℝ} (hv_lo : (17 / 5 : ℝ) ^ 2 ≤ v) (hv_hi : v ≤ (183 / 50) ^ 2) :
    HDeriv2 v ≤ (7 / 20) / v ^ 2 := by
  have hv0 : 0 < v := by linarith
  rw [HDeriv2_eq_fHpp hv0]
  have hx_lo : (17 / 5 : ℝ) ≤ Real.sqrt v := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 17 / 5)]; exact Real.sqrt_le_sqrt hv_lo
  have hx_hi : Real.sqrt v ≤ 183 / 50 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 183 / 50)]; exact Real.sqrt_le_sqrt hv_hi
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hanti := fHpp_antitone_q1 (a := 17 / 5) (b := 183 / 50) (by norm_num) (by norm_num)
    (fun t ht => by
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t ht => by
      rw [← Real.cos_sub_two_pi]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hf := le_trans (hanti ⟨le_rfl, by norm_num⟩ ⟨hx_lo, hx_hi⟩ hx_lo) fHpp_at_340
  have hstep : fHpp (Real.sqrt v) / (4 * v ^ 2) ≤ (7 / 5) / (4 * v ^ 2) :=
    div_le_div_of_nonneg_right hf (by positivity)
  have heq : (7 / 5 : ℝ) / (4 * v ^ 2) = (7 / 20) / v ^ 2 := by ring
  linarith

private theorem HDeriv2_Z1 {v : ℝ} (hv_lo : (183 / 50 : ℝ) ^ 2 ≤ v) (hv_hi : v ≤ (261 / 50) ^ 2) :
    HDeriv2 v ≤ 0 := by
  have hv0 : 0 < v := by linarith
  rw [HDeriv2_eq_fHpp hv0]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  set x := Real.sqrt v
  have hx_lo : (183 / 50 : ℝ) ≤ x := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 183 / 50)]; exact Real.sqrt_le_sqrt hv_lo
  have hx_hi : x ≤ 261 / 50 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 261 / 50)]; exact Real.sqrt_le_sqrt hv_hi
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases h1 : x ≤ 5 * Real.pi / 4
  · have hanti := fHpp_antitone_q1 (a := 183 / 50) (b := 5 * Real.pi / 4) (by norm_num) (by linarith)
      (fun t ht => by
        rw [← Real.sin_sub_two_pi]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2]))
      (fun t ht => by
        rw [← Real.cos_sub_two_pi]
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact le_trans (hanti ⟨le_rfl, by linarith⟩ ⟨hx_lo, h1⟩ hx_lo) fHpp_at_366
  · push Not at h1
    by_cases h2 : x ≤ 3 * Real.pi / 2
    · refine fHpp_nonpos_q2 (by linarith) ?_ ?_
      · rw [cos_shift_3pi, ← Real.cos_neg, show -(2 * x - 3 * Real.pi) = 3 * Real.pi - 2 * x by ring]
        have hnn := Real.cos_nonneg_of_mem_Icc ⟨(by linarith : -(Real.pi / 2) ≤ 3 * Real.pi - 2 * x), by linarith⟩
        linarith
      · rw [← Real.sin_sub_two_pi]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    · push Not at h2
      have hmono := fHpp_monotone_q3 (a := 3 * Real.pi / 2) (b := 261 / 50) (by linarith) (by linarith)
        (fun t ht => by
          rw [sin_shift_3pi]
          have := Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * t - 3 * Real.pi)
            (by linarith [ht.1]) (by linarith [ht.2])
          linarith)
        (fun t ht => by
          rw [cos_shift_3pi]
          have := Real.cos_nonneg_of_mem_Icc (x := 2 * t - 3 * Real.pi)
            ⟨by linarith [ht.1], by linarith [ht.2]⟩
          linarith)
      exact le_trans (hmono ⟨h2.le, hx_hi⟩ ⟨by linarith, le_rfl⟩ hx_hi) fHpp_at_522

private theorem HDeriv2_Z2 {v : ℝ} (hv_lo : (261 / 50 : ℝ) ^ 2 ≤ v) (hv_hi : v ≤ (28 / 5) ^ 2) :
    HDeriv2 v ≤ (7 / 20) / v ^ 2 := by
  have hv0 : 0 < v := by linarith
  rw [HDeriv2_eq_fHpp hv0]
  set x := Real.sqrt v
  have hx_lo : (261 / 50 : ℝ) ≤ x := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 261 / 50)]; exact Real.sqrt_le_sqrt hv_lo
  have hx_hi : x ≤ 28 / 5 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 28 / 5)]; exact Real.sqrt_le_sqrt hv_hi
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hmono : MonotoneOn fHpp (Set.Icc (261 / 50) (28 / 5)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · intro t ht; exact (hasDerivAt_fHpp (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht; exact (hasDerivAt_fHpp (by linarith [(interior_subset ht).1])).differentiableAt.differentiableWithinAt
    · intro t ht
      have htm := interior_subset ht
      have ht0 : 0 < t := by linarith [htm.1]
      rw [(hasDerivAt_fHpp ht0).deriv]
      have hsin_ub : Real.sin (2 * t) ≤ -(80 / 100) := by
        rw [sin_shift_3pi]
        by_cases hmid : 2 * t - 3 * Real.pi ≤ Real.pi / 2
        · have h1 := sin_monotone_Icc (by linarith) (by linarith [htm.1] : (1 : ℝ) ≤ 2 * t - 3 * Real.pi) hmid
          have h2 := sin_lb_ord4 (by norm_num : (0 : ℝ) ≤ 1)
          norm_num at h2; linarith
        · push Not at hmid
          have hsym : Real.sin (2 * t - 3 * Real.pi) = Real.sin (4 * Real.pi - 2 * t) := by
            rw [← Real.sin_pi_sub]; congr 1; ring
          rw [hsym]
          have h1 := sin_monotone_Icc (by linarith) (by linarith [htm.2] : (136 / 100 : ℝ) ≤ 4 * Real.pi - 2 * t) (by linarith)
          have h2 := sin_lb_ord4 (by norm_num : (0 : ℝ) ≤ 136 / 100)
          norm_num at h2; linarith
      have hcos_ub : Real.cos (2 * t) ≤ 25 / 100 := by
        rw [cos_shift_4pi, ← Real.cos_neg, show -(2 * t - 4 * Real.pi) = 4 * Real.pi - 2 * t by ring]
        have h1 := cos_antitone_Icc (by norm_num) (by linarith [htm.2] : (136 / 100 : ℝ) ≤ 4 * Real.pi - 2 * t) (by linarith [htm.1])
        have h2 := cos_ub_ord4 (by norm_num : (0 : ℝ) ≤ 136 / 100)
        norm_num at h2; linarith
      have ht2 : (25 : ℝ) ≤ t ^ 2 := by nlinarith [htm.1]
      have h1 : 13 / t ^ 2 ≤ 1 := by rw [div_le_one (sq_pos_of_pos ht0)]; linarith
      have h2 : 10 / t - 8 / t ^ 3 ≤ 2 := by
        have : 10 / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith [htm.1]
        have : (0 : ℝ) ≤ 8 / t ^ 3 := by positivity
        linarith
      have h2_nn : 0 ≤ 10 / t - 8 / t ^ 3 := by
        rw [sub_nonneg, div_le_div_iff₀ (pow_pos ht0 3) ht0]; nlinarith [htm.1]
      have h3 : 8 / t ^ 3 ≤ 1 / 10 := by
        rw [div_le_div_iff₀ (pow_pos ht0 3) (by norm_num)]; nlinarith [htm.1]
      nlinarith
  have hf := le_trans (hmono ⟨hx_lo, hx_hi⟩ ⟨by norm_num, le_rfl⟩ hx_hi) fHpp_at_560
  have hstep : fHpp x / (4 * v ^ 2) ≤ (7 / 5) / (4 * v ^ 2) :=
    div_le_div_of_nonneg_right hf (by positivity)
  have heq : (7 / 5 : ℝ) / (4 * v ^ 2) = (7 / 20) / v ^ 2 := by ring
  linarith

private theorem HDeriv2_Z4 {v : ℝ} (hv_lo : (131 / 20 : ℝ) ^ 2 ≤ v) (hv_hi : v ≤ (691 / 100) ^ 2) :
    HDeriv2 v ≤ (7 / 20) / v ^ 2 := by
  have hv0 : 0 < v := by linarith
  rw [HDeriv2_eq_fHpp hv0]
  have hx_lo : (131 / 20 : ℝ) ≤ Real.sqrt v := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 131 / 20)]; exact Real.sqrt_le_sqrt hv_lo
  have hx_hi : Real.sqrt v ≤ 691 / 100 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 691 / 100)]; exact Real.sqrt_le_sqrt hv_hi
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hanti := fHpp_antitone_q1 (a := 131 / 20) (b := 691 / 100) (by norm_num) (by norm_num)
    (fun t ht => by
      rw [sin_shift_4pi]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2]))
    (fun t ht => by
      rw [cos_shift_4pi]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hf := le_trans (hanti ⟨le_rfl, by norm_num⟩ ⟨hx_lo, hx_hi⟩ hx_lo) fHpp_at_655
  have hstep : fHpp (Real.sqrt v) / (4 * v ^ 2) ≤ (7 / 5) / (4 * v ^ 2) :=
    div_le_div_of_nonneg_right hf (by positivity)
  have heq : (7 / 5 : ℝ) / (4 * v ^ 2) = (7 / 20) / v ^ 2 := by ring
  linarith

private theorem HDeriv2_Z5 {v : ℝ} (hv_lo : (691 / 100 : ℝ) ^ 2 ≤ v) (hv_hi : v ≤ (847 / 100) ^ 2) :
    HDeriv2 v ≤ 0 := by
  have hv0 : 0 < v := by linarith
  rw [HDeriv2_eq_fHpp hv0]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  set x := Real.sqrt v
  have hx_lo : (691 / 100 : ℝ) ≤ x := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 691 / 100)]; exact Real.sqrt_le_sqrt hv_lo
  have hx_hi : x ≤ 847 / 100 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 847 / 100)]; exact Real.sqrt_le_sqrt hv_hi
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases h1 : x ≤ 9 * Real.pi / 4
  · have hanti := fHpp_antitone_q1 (a := 691 / 100) (b := 9 * Real.pi / 4) (by norm_num) (by linarith)
      (fun t ht => by
        rw [sin_shift_4pi]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2]))
      (fun t ht => by
        rw [cos_shift_4pi]
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact le_trans (hanti ⟨le_rfl, by linarith⟩ ⟨hx_lo, h1⟩ hx_lo) fHpp_at_691
  · push Not at h1
    by_cases h2 : x ≤ 5 * Real.pi / 2
    · refine fHpp_nonpos_q2 (by linarith) ?_ ?_
      · rw [cos_shift_5pi, ← Real.cos_neg, show -(2 * x - 5 * Real.pi) = 5 * Real.pi - 2 * x by ring]
        have hnn := Real.cos_nonneg_of_mem_Icc ⟨(by linarith : -(Real.pi / 2) ≤ 5 * Real.pi - 2 * x), by linarith⟩
        linarith
      · rw [sin_shift_4pi]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    · push Not at h2
      have hmono := fHpp_monotone_q3 (a := 5 * Real.pi / 2) (b := 847 / 100) (by linarith) (by linarith)
        (fun t ht => by
          rw [sin_shift_5pi]
          have := Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * t - 5 * Real.pi)
            (by linarith [ht.1]) (by linarith [ht.2])
          linarith)
        (fun t ht => by
          rw [cos_shift_5pi]
          have := Real.cos_nonneg_of_mem_Icc (x := 2 * t - 5 * Real.pi)
            ⟨by linarith [ht.1], by linarith [ht.2]⟩
          linarith)
      exact le_trans (hmono ⟨h2.le, hx_hi⟩ ⟨by linarith, le_rfl⟩ hx_hi) fHpp_at_847

/-! ### 7. Taylor Integral Representation & Rational Segment Bounds (`phi2`, `phi3`) -/

private theorem Hww_eq_taylor_integral {w1 w : ℝ} (hw1 : 0 < w1) (hw1w : w1 < w) :
    (w - w1) ^ 2 * Hww w1 w = ∫ v in w1..w, (v - w1) * HDeriv2 v := by
  let F : ℝ → ℝ := fun v => (v - w1) * HDeriv v - H v
  have hF : ∀ v ∈ Set.uIcc w1 w, HasDerivAt F ((v - w1) * HDeriv2 v) v := by
    intro v hv
    rw [Set.uIcc_of_le hw1w.le] at hv
    have hv0 : 0 < v := lt_of_lt_of_le hw1 hv.1
    have h1 := ((hasDerivAt_id' v).sub_const w1).fun_mul (hasDerivAt_HDeriv hv0)
    have h2 := hasDerivAt_H hv0
    refine (h1.fun_sub h2).congr_deriv ?_; ring
  have hint : IntervalIntegrable (fun v => (v - w1) * HDeriv2 v) MeasureTheory.volume w1 w := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hw1w.le]
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hw1 hv.1
    have hc : ContinuousAt HDeriv2 v := (hasDerivAt_HDeriv2 hv0).continuousAt
    exact ((continuousAt_id.sub continuousAt_const).mul hc).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  unfold Hww
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 (sub_pos.mpr hw1w).ne')]
  simp only [F, sub_self, zero_mul, zero_sub]
  ring

private theorem log_sq_le_sub_inv {r : ℝ} (hr : 1 ≤ r) :
    Real.log (r ^ 2) ≤ r - 1 / r := by
  let g : ℝ → ℝ := fun t => t - 1 / t - 2 * Real.log t
  have hgd : ∀ t : ℝ, 0 < t → HasDerivAt g (1 + 1 / t ^ 2 - 2 / t) t := by
    intro t ht0
    have h1 := hasDerivAt_id' t
    have h2 := hasDerivAt_inv_real ht0.ne'
    have h3 := (Real.hasDerivAt_log ht0.ne').const_mul (2 : ℝ)
    refine ((h1.fun_sub h2).fun_sub h3).congr_deriv ?_; ring
  have hg : MonotoneOn g (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
    · intro t ht; exact (hgd t (by linarith [Set.mem_Ici.mp ht])).continuousAt.continuousWithinAt
    · intro t ht; exact (hgd t (by linarith [Set.mem_Ici.mp (interior_subset ht)])).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : (0 : ℝ) < t := by linarith [Set.mem_Ici.mp (interior_subset ht)]
      rw [(hgd t ht0).deriv]
      have : 1 + 1 / t ^ 2 - 2 / t = (1 - 1 / t) ^ 2 := by field_simp [ht0.ne']; ring
      rw [this]; positivity
  have h0 := hg (le_rfl : (1 : ℝ) ∈ Set.Ici 1) hr hr
  simp only [g, div_one, sub_self, Real.log_one, mul_zero] at h0
  rw [Real.log_pow]; push_cast; linarith

private theorem int_v2_le_phi2 {x1 a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) / v ^ 2 ≤ phi2 x1 a b := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  let F : ℝ → ℝ := fun v => Real.log v + x1 ^ 2 / v
  have hF : ∀ v ∈ Set.uIcc (a ^ 2) (b ^ 2), HasDerivAt F ((v - x1 ^ 2) / v ^ 2) v := by
    intro v hv
    rw [Set.uIcc_of_le ha2b2] at hv
    have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
    have h1 := Real.hasDerivAt_log hv0.ne'
    have h2 : HasDerivAt (fun s : ℝ => x1 ^ 2 / s) (x1 ^ 2 * (-1 / v ^ 2)) v := by
      have : (fun s : ℝ => x1 ^ 2 / s) = fun s => x1 ^ 2 * (1 / s) := by funext s; ring
      rw [this]; exact (hasDerivAt_inv_real hv0.ne').const_mul (x1 ^ 2)
    refine (h1.fun_add h2).congr_deriv ?_; field_simp [hv0.ne']; ring
  have hint : IntervalIntegrable (fun v => (v - x1 ^ 2) / v ^ 2) MeasureTheory.volume (a ^ 2) (b ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha2b2]
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
    exact ((continuousAt_id.sub continuousAt_const).div (continuousAt_id.pow 2) (pow_ne_zero 2 hv0.ne')).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F]
  have hlog : Real.log (b ^ 2) - Real.log (a ^ 2) ≤ (b ^ 2 - a ^ 2) / (a * b) := by
    rw [← Real.log_div (sq_pos_of_pos hb0).ne' ha2.ne', ← div_pow]
    have hr : 1 ≤ b / a := (one_le_div ha).mpr hab
    have h := log_sq_le_sub_inv hr
    have heq : b / a - 1 / (b / a) = (b ^ 2 - a ^ 2) / (a * b) := by
      field_simp [ha.ne', hb0.ne']
    linarith
  have hphi : (b ^ 2 - a ^ 2) / (a * b) + x1 ^ 2 / b ^ 2 - x1 ^ 2 / a ^ 2 = phi2 x1 a b := by
    unfold phi2; field_simp [ha.ne', hb0.ne']; ring
  linarith

private theorem int_v3_eq_phi3 {x1 a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) / v ^ 3 = phi3 x1 a b := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  let F : ℝ → ℝ := fun v => -1 / v + x1 ^ 2 / (2 * v ^ 2)
  have hF : ∀ v ∈ Set.uIcc (a ^ 2) (b ^ 2), HasDerivAt F ((v - x1 ^ 2) / v ^ 3) v := by
    intro v hv
    rw [Set.uIcc_of_le ha2b2] at hv
    have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
    have h1 : HasDerivAt (fun s : ℝ => -1 / s) (1 / v ^ 2) v := by
      have : (fun s : ℝ => -1 / s) = fun s => (-1 : ℝ) * (1 / s) := by funext s; ring
      rw [this]; refine ((hasDerivAt_inv_real hv0.ne').const_mul (-1 : ℝ)).congr_deriv ?_; ring
    have h2 : HasDerivAt (fun s : ℝ => x1 ^ 2 / (2 * s ^ 2)) (-x1 ^ 2 / v ^ 3) v := by
      have : (fun s : ℝ => x1 ^ 2 / (2 * s ^ 2)) = fun s => (x1 ^ 2 / 2) * (1 / s ^ 2) := by funext s; ring
      rw [this]
      refine ((hasDerivAt_inv_sq_real hv0.ne').const_mul (x1 ^ 2 / 2)).congr_deriv ?_
      field_simp [hv0.ne']
    refine (h1.fun_add h2).congr_deriv ?_; field_simp [hv0.ne']; ring
  have hint : IntervalIntegrable (fun v => (v - x1 ^ 2) / v ^ 3) MeasureTheory.volume (a ^ 2) (b ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha2b2]
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
    exact ((continuousAt_id.sub continuousAt_const).div (continuousAt_id.pow 3) (pow_ne_zero 3 hv0.ne')).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F]; unfold phi3; field_simp [ha.ne', hb0.ne']; ring

private theorem seg_int_le_zero {x1 a b : ℝ} (hx1 : 0 < x1) (hx1a : x1 ≤ a) (hab : a ≤ b)
    (hM : ∀ v ∈ Set.Icc (a ^ 2) (b ^ 2), HDeriv2 v ≤ 0) :
    ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤ 0 := by
  have ha : 0 < a := lt_of_lt_of_le hx1 hx1a
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  have h0 : (0 : ℝ) = ∫ _ in a ^ 2..b ^ 2, (0 : ℝ) := by simp
  rw [h0]
  refine intervalIntegral.integral_mono_on ha2b2 ?_ intervalIntegrable_const fun v hv => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha2b2]
    intro v hv
    exact ((continuousAt_id.sub continuousAt_const).mul
      (hasDerivAt_HDeriv2 (lt_of_lt_of_le ha2 hv.1)).continuousAt).continuousWithinAt
  · exact mul_nonpos_of_nonneg_of_nonpos (by nlinarith [hv.1]) (hM v hv)

private theorem seg_int_le_c2 {x1 a b c2 : ℝ} (hx1 : 0 < x1) (hx1a : x1 ≤ a) (hab : a ≤ b) (hc2 : 0 ≤ c2)
    (hM : ∀ v ∈ Set.Icc (a ^ 2) (b ^ 2), HDeriv2 v ≤ c2 / v ^ 2) :
    ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤ c2 * phi2 x1 a b := by
  have ha : 0 < a := lt_of_lt_of_le hx1 hx1a
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  have h1 : ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
      ∫ v in a ^ 2..b ^ 2, c2 * ((v - x1 ^ 2) / v ^ 2) := by
    refine intervalIntegral.integral_mono_on ha2b2 ?_ ?_ fun v hv => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le ha2b2]; intro v hv
      exact ((continuousAt_id.sub continuousAt_const).mul
        (hasDerivAt_HDeriv2 (lt_of_lt_of_le ha2 hv.1)).continuousAt).continuousWithinAt
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le ha2b2]; intro v hv
      have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
      exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).div
        (continuousAt_id.pow 2) (pow_ne_zero 2 hv0.ne'))).continuousWithinAt
    · have hnn : 0 ≤ v - x1 ^ 2 := by nlinarith [hv.1]
      have hmul := mul_le_mul_of_nonneg_left (hM v hv) hnn
      linarith [show (v - x1 ^ 2) * (c2 / v ^ 2) = c2 * ((v - x1 ^ 2) / v ^ 2) by ring]
  rw [intervalIntegral.integral_const_mul] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left (int_v2_le_phi2 ha hab) hc2)

private theorem seg_int_le_cs {x1 a b : ℝ} (hx1 : 0 < x1) (hx1a : x1 ≤ a) (hab : a ≤ b)
    (ha_cs : 7 / 3 ≤ a ^ 2) :
    ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
      (1 / 2) * phi2 x1 a b + (7 / 4) * phi3 x1 a b := by
  have ha : 0 < a := lt_of_lt_of_le hx1 hx1a
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hi2 : IntervalIntegrable (fun v => (1 / 2 : ℝ) * ((v - x1 ^ 2) / v ^ 2))
      MeasureTheory.volume (a ^ 2) (b ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha2b2]; intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
    exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hv0.ne'))).continuousWithinAt
  have hi3 : IntervalIntegrable (fun v => (7 / 4 : ℝ) * ((v - x1 ^ 2) / v ^ 3))
      MeasureTheory.volume (a ^ 2) (b ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ha2b2]; intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le ha2 hv.1
    exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.pow 3) (pow_ne_zero 3 hv0.ne'))).continuousWithinAt
  have h1 : ∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
      ∫ v in a ^ 2..b ^ 2, ((1 / 2 : ℝ) * ((v - x1 ^ 2) / v ^ 2) + (7 / 4) * ((v - x1 ^ 2) / v ^ 3)) := by
    refine intervalIntegral.integral_mono_on ha2b2 ?_ (hi2.add hi3) fun v hv => ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le ha2b2]; intro v hv
      exact ((continuousAt_id.sub continuousAt_const).mul
        (hasDerivAt_HDeriv2 (lt_of_lt_of_le ha2 hv.1)).continuousAt).continuousWithinAt
    · have hnn : 0 ≤ v - x1 ^ 2 := by nlinarith [hv.1]
      have hM := HDeriv2_le_global_cs (le_trans ha_cs hv.1)
      have hmul := mul_le_mul_of_nonneg_left hM hnn
      linarith [show (v - x1 ^ 2) * (1 / (2 * v ^ 2) + 7 / (4 * v ^ 3)) =
        (1 / 2) * ((v - x1 ^ 2) / v ^ 2) + (7 / 4) * ((v - x1 ^ 2) / v ^ 3) by ring]
  rw [intervalIntegral.integral_add hi2 hi3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, int_v3_eq_phi3 ha hab] at h1
  have h2 := int_v2_le_phi2 (x1 := x1) ha hab
  linarith

private theorem int_split {x1 a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ v in a ^ 2..c ^ 2, (v - x1 ^ 2) * HDeriv2 v =
      (∫ v in a ^ 2..b ^ 2, (v - x1 ^ 2) * HDeriv2 v) +
      (∫ v in b ^ 2..c ^ 2, (v - x1 ^ 2) * HDeriv2 v) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have h1 : IntervalIntegrable (fun v => (v - x1 ^ 2) * HDeriv2 v) MeasureTheory.volume (a ^ 2) (b ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by nlinarith : a ^ 2 ≤ b ^ 2)]; intro v hv
    exact ((continuousAt_id.sub continuousAt_const).mul
      (hasDerivAt_HDeriv2 (lt_of_lt_of_le ha2 hv.1)).continuousAt).continuousWithinAt
  have h2 : IntervalIntegrable (fun v => (v - x1 ^ 2) * HDeriv2 v) MeasureTheory.volume (b ^ 2) (c ^ 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by nlinarith : b ^ 2 ≤ c ^ 2)]; intro v hv
    exact ((continuousAt_id.sub continuousAt_const).mul
      (hasDerivAt_HDeriv2 (lt_of_lt_of_le (sq_pos_of_pos hb0) hv.1)).continuousAt).continuousWithinAt
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

private theorem Hww_lt_of_taylor {u x1 x L B : ℝ}
    (hu0 : 0 < u) (hu : u < Real.pi / 2) (hx1 : 0 < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hL : L < x ^ 4 * Hww ((Real.pi / 2) ^ 2) (x ^ 2))
    (hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤ B)
    (hB : x ^ 4 * B < L * (x ^ 2 - x1 ^ 2) ^ 2) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx0 : 0 < x := lt_trans hx1 hx1x
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have hu_lt_pi2 : u ^ 2 < (Real.pi / 2) ^ 2 := by nlinarith
  have hpi2_le : (Real.pi / 2) ^ 2 ≤ 25 / 4 := by nlinarith [Real.pi_pos]
  have hstep1 : Hww ((Real.pi / 2) ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) :=
    Hww_strictAnti_case1 (sq_pos_of_pos hu0) hu_lt_pi2 hpi2_le (by rw [Real.sqrt_sq hx0.le]; exact hx_ge)
  have hT := Hww_eq_taylor_integral (sq_pos_of_pos hx1) (by nlinarith : x1 ^ 2 < x ^ 2)
  have hdiff_pos : 0 < (x ^ 2 - x1 ^ 2) ^ 2 := sq_pos_of_pos (by nlinarith)
  have hx4_pos : 0 < x ^ 4 := by positivity
  have h1 : x ^ 4 * ((x ^ 2 - x1 ^ 2) ^ 2 * Hww (x1 ^ 2) (x ^ 2)) < L * (x ^ 2 - x1 ^ 2) ^ 2 := by
    rw [hT]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hI hx4_pos.le) hB
  have h2 : L * (x ^ 2 - x1 ^ 2) ^ 2 < (x ^ 4 * Hww ((Real.pi / 2) ^ 2) (x ^ 2)) * (x ^ 2 - x1 ^ 2) ^ 2 :=
    mul_lt_mul_of_pos_right hL hdiff_pos
  have h3 : Hww (x1 ^ 2) (x ^ 2) < Hww ((Real.pi / 2) ^ 2) (x ^ 2) := by
    have hK : 0 < x ^ 4 * (x ^ 2 - x1 ^ 2) ^ 2 := mul_pos hx4_pos hdiff_pos
    nlinarith only [h1, h2, hK]
  exact lt_trans h3 hstep1

/-! ### 8. Modular Zone Helpers for Case 2 (`x1 > 5/2`, `x > 83/20`) -/

private theorem case2_Z0 {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 17 / 5 ≤ x1) (hhi : x1 ≤ 183 / 50) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases hx_522 : x ≤ 261 / 50
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤ (7 / 20) * phi2 x1 x1 (183 / 50) := by
      rw [int_split hx1_pos hhi (by linarith)]
      have i1 := seg_int_le_c2 hx1_pos le_rfl hhi (by norm_num)
        (fun v hv => HDeriv2_Z0 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_zero hx1_pos hhi (by linarith : (183 / 50 : ℝ) ≤ x)
        (fun v hv => HDeriv2_Z1 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z0_Z1 hlo hhi hx_ge hx_522)
  · push Not at hx_522
    exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 17 / 5) (b1 := 183 / 50) (x_lo := 261 / 50)
      (s_max := 52 / 100) (by norm_num) hlo hhi (by norm_num) hx_522.le (by norm_num)
      (le_trans (abs_sin_le_abs_sub_pi x1) (abs_le.mpr ⟨by linarith, by linarith⟩)) (by norm_num)

private theorem abs_sin_le_of_two_pi_sub {x1 y s : ℝ}
    (hx_lo : 3 * Real.pi / 2 ≤ x1) (hx_hi : x1 ≤ 2 * Real.pi)
    (hy : 2 * Real.pi - x1 ≤ y) (hy_le : y ≤ Real.pi / 2)
    (hs : y - y ^ 3 / 6 + y ^ 5 / 120 ≤ s) :
    |Real.sin x1| ≤ s := by
  have hshift : Real.sin x1 = -Real.sin (2 * Real.pi - x1) := by
    have h1 := Real.sin_sub_two_pi x1
    have h2 : x1 - 2 * Real.pi = -(2 * Real.pi - x1) := by ring
    rw [← h1, h2, Real.sin_neg]
  rw [hshift, abs_neg]
  have hnn : 0 ≤ Real.sin (2 * Real.pi - x1) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [abs_of_nonneg hnn]
  have hmono := sin_monotone_Icc (by linarith : -(Real.pi / 2) ≤ 2 * Real.pi - x1) hy hy_le
  have hub := sin_ub_ord3 (by linarith : 0 ≤ y)
  linarith

private theorem abs_sin_le_of_three_pi_sub {x1 y s : ℝ}
    (hx_lo : 5 * Real.pi / 2 ≤ x1) (hx_hi : x1 ≤ 3 * Real.pi)
    (hy : 3 * Real.pi - x1 ≤ y) (hy_le : y ≤ Real.pi / 2)
    (hs : y - y ^ 3 / 6 + y ^ 5 / 120 ≤ s) :
    |Real.sin x1| ≤ s := by
  have hshift : Real.sin x1 = Real.sin (3 * Real.pi - x1) := by
    rw [sin_shift_3pi x1, show x1 - 3 * Real.pi = -(3 * Real.pi - x1) by ring, Real.sin_neg, neg_neg]
  rw [hshift]
  have hnn : 0 ≤ Real.sin (3 * Real.pi - x1) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [abs_of_nonneg hnn]
  have hmono := sin_monotone_Icc (by linarith : -(Real.pi / 2) ≤ 3 * Real.pi - x1) hy hy_le
  have hub := sin_ub_ord3 (by linarith : 0 ≤ y)
  linarith

private theorem case2_Z1 {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 183 / 50 ≤ x1) (hhi : x1 ≤ 261 / 50) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases hx_522 : x ≤ 261 / 50
  · have hI := seg_int_le_zero hx1_pos le_rfl hx1x.le
      (fun v hv => HDeriv2_Z1 (le_trans (by nlinarith) hv.1) (le_trans hv.2 (by nlinarith)))
    have hdiff : 0 < x ^ 2 - x1 ^ 2 := by nlinarith
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (by rw [mul_zero]; positivity)
  push Not at hx_522
  by_cases hx_560 : x ≤ 28 / 5
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤ (7 / 20) * phi2 x1 (261 / 50) x := by
      rw [int_split hx1_pos hhi hx_522.le]
      have i1 := seg_int_le_zero hx1_pos le_rfl hhi (fun v hv => HDeriv2_Z1 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_c2 hx1_pos hhi hx_522.le (by norm_num)
        (fun v hv => HDeriv2_Z2 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z1_Z2 hlo hhi hx_522.le hx_560 hx1x)
  push Not at hx_560
  by_cases hx_600 : x ≤ 6
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (7 / 20) * phi2 x1 (261 / 50) (28 / 5) +
        (1 / 2) * phi2 x1 (28 / 5) x + (7 / 4) * phi3 x1 (28 / 5) x := by
      rw [int_split hx1_pos hhi (by linarith),
          int_split (by norm_num) (by norm_num : (261 / 50 : ℝ) ≤ 28 / 5) hx_560.le]
      have i1 := seg_int_le_zero hx1_pos le_rfl hhi (fun v hv => HDeriv2_Z1 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_c2 hx1_pos hhi (by norm_num) (by norm_num) (fun v hv => HDeriv2_Z2 hv.1 hv.2)
      have i3 := seg_int_le_cs (a := 28 / 5) (b := x) hx1_pos (by linarith) hx_560.le (by norm_num)
      linarith only [i1, i2, i3]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z1_Z3a hlo hhi hx_560.le hx_600)
  push Not at hx_600
  by_cases hx_655 : x ≤ 131 / 20
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (7 / 20) * phi2 x1 (261 / 50) (28 / 5) +
        (1 / 2) * phi2 x1 (28 / 5) x + (7 / 4) * phi3 x1 (28 / 5) x := by
      rw [int_split hx1_pos hhi (by linarith),
          int_split (by norm_num) (by norm_num : (261 / 50 : ℝ) ≤ 28 / 5) (by linarith)]
      have i1 := seg_int_le_zero hx1_pos le_rfl hhi (fun v hv => HDeriv2_Z1 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_c2 hx1_pos hhi (by norm_num) (by norm_num) (fun v hv => HDeriv2_Z2 hv.1 hv.2)
      have i3 := seg_int_le_cs (a := 28 / 5) (b := x) hx1_pos (by linarith) (by linarith) (by norm_num)
      linarith only [i1, i2, i3]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 hx_600.le (by linarith)) hI
      (cert_Z1_Z3b hlo hhi hx_600.le hx_655)
  push Not at hx_655
  by_cases hx_675 : x ≤ 27 / 4
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (7 / 20) * phi2 x1 (261 / 50) (28 / 5) +
        (1 / 2) * phi2 x1 (28 / 5) (131 / 20) + (7 / 4) * phi3 x1 (28 / 5) (131 / 20) +
        (7 / 20) * phi2 x1 (131 / 20) x := by
      rw [int_split hx1_pos hhi (by linarith),
          int_split (by norm_num) (by norm_num : (261 / 50 : ℝ) ≤ 28 / 5) (by linarith),
          int_split (by norm_num) (by norm_num : (28 / 5 : ℝ) ≤ 131 / 20) hx_655.le]
      have i1 := seg_int_le_zero hx1_pos le_rfl hhi (fun v hv => HDeriv2_Z1 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_c2 hx1_pos hhi (by norm_num) (by norm_num) (fun v hv => HDeriv2_Z2 hv.1 hv.2)
      have i3 := seg_int_le_cs (a := 28 / 5) (b := 131 / 20) hx1_pos (by linarith) (by norm_num) (by norm_num)
      have i4 := seg_int_le_c2 (a := 131 / 20) (b := x) hx1_pos (by linarith) hx_655.le (by norm_num)
        (fun v hv => HDeriv2_Z4 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2, i3, i4]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 (by linarith) hx_675) hI
      (cert_Z1_Z4a hlo hhi hx_655.le hx_675)
  · push Not at hx_675
    by_cases hx1_410 : x1 ≤ 41 / 10
    · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 183 / 50) (b1 := 41 / 10) (x_lo := 27 / 4)
        (s_max := 96 / 100) (by norm_num) hlo hx1_410 (by norm_num) hx_675.le (by norm_num)
        (le_trans (abs_sin_le_abs_sub_pi x1) (abs_le.mpr ⟨by linarith, by linarith⟩)) (by norm_num)
    · push Not at hx1_410
      by_cases hx1_470 : x1 ≤ 47 / 10
      · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 41 / 10) (b1 := 47 / 10) (x_lo := 27 / 4)
          (s_max := 1) (by norm_num) hx1_410.le hx1_470 (by norm_num) hx_675.le (by norm_num)
          (Real.abs_sin_le_one x1) (by norm_num)
      · push Not at hx1_470
        exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 47 / 10) (b1 := 261 / 50) (x_lo := 27 / 4)
          (s_max := 1) (by norm_num) hx1_470.le hhi (by norm_num) hx_675.le (by norm_num)
          (Real.abs_sin_le_one x1) (by norm_num)

private theorem case2_Z2 {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 261 / 50 ≤ x1) (hhi : x1 ≤ 28 / 5) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases hx_560 : x ≤ 28 / 5
  · have hI := seg_int_le_c2 hx1_pos le_rfl hx1x.le (by norm_num)
      (fun v hv => HDeriv2_Z2 (le_trans (by nlinarith) hv.1) (le_trans hv.2 (by nlinarith)))
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z2_diag hlo hx1x hx_560)
  push Not at hx_560
  by_cases hx_600 : x ≤ 6
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (7 / 20) * phi2 x1 x1 (28 / 5) +
        (1 / 2) * phi2 x1 (28 / 5) x + (7 / 4) * phi3 x1 (28 / 5) x := by
      rw [int_split hx1_pos hhi hx_560.le]
      have i1 := seg_int_le_c2 hx1_pos le_rfl hhi (by norm_num)
        (fun v hv => HDeriv2_Z2 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_cs hx1_pos hhi hx_560.le (by norm_num)
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z2_Z3a hlo hhi hx_560.le hx_600 hx1x)
  push Not at hx_600
  by_cases hx_655 : x ≤ 131 / 20
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (7 / 20) * phi2 x1 x1 (28 / 5) +
        (1 / 2) * phi2 x1 (28 / 5) x + (7 / 4) * phi3 x1 (28 / 5) x := by
      rw [int_split hx1_pos hhi (by linarith)]
      have i1 := seg_int_le_c2 hx1_pos le_rfl hhi (by norm_num)
        (fun v hv => HDeriv2_Z2 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_cs (a := 28 / 5) (b := x) hx1_pos hhi (by linarith) (by norm_num)
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 hx_600.le (by linarith)) hI
      (cert_Z2_Z3b hlo hhi hx_600.le hx_655)
  push Not at hx_655
  by_cases hx_675 : x ≤ 27 / 4
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (7 / 20) * phi2 x1 x1 (28 / 5) +
        (1 / 2) * phi2 x1 (28 / 5) (131 / 20) + (7 / 4) * phi3 x1 (28 / 5) (131 / 20) +
        (7 / 20) * phi2 x1 (131 / 20) x := by
      rw [int_split hx1_pos hhi (by linarith),
          int_split (by norm_num) (by norm_num : (28 / 5 : ℝ) ≤ 131 / 20) hx_655.le]
      have i1 := seg_int_le_c2 hx1_pos le_rfl hhi (by norm_num)
        (fun v hv => HDeriv2_Z2 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_cs (a := 28 / 5) (b := 131 / 20) hx1_pos hhi (by norm_num) (by norm_num)
      have i3 := seg_int_le_c2 (a := 131 / 20) (b := x) hx1_pos (by linarith) hx_655.le (by norm_num)
        (fun v hv => HDeriv2_Z4 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2, i3]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 (by linarith) hx_675) hI
      (cert_Z2_Z4a hlo hhi hx_655.le hx_675)
  · push Not at hx_675
    by_cases hx1_530 : x1 ≤ 53 / 10
    · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 261 / 50) (b1 := 53 / 10) (x_lo := 27 / 4)
        (s_max := 1) (by norm_num) hlo hx1_530 (by norm_num) hx_675.le (by norm_num)
        (Real.abs_sin_le_one x1) (by norm_num)
    · push Not at hx1_530
      by_cases hx1_545 : x1 ≤ 109 / 20
      · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 53 / 10) (b1 := 109 / 20) (x_lo := 27 / 4)
          (s_max := 84 / 100) (by norm_num) hx1_530.le hx1_545 (by norm_num) hx_675.le (by norm_num)
          (abs_sin_le_of_two_pi_sub (y := 9832 / 10000) (by linarith) (by linarith) (by linarith)
            (by linarith) (by norm_num)) (by norm_num)
      · push Not at hx1_545
        exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 109 / 20) (b1 := 28 / 5) (x_lo := 27 / 4)
          (s_max := 75 / 100) (by norm_num) hx1_545.le hhi (by norm_num) hx_675.le (by norm_num)
          (abs_sin_le_of_two_pi_sub (y := 8332 / 10000) (by linarith) (by linarith) (by linarith)
            (by linarith) (by norm_num)) (by norm_num)

private theorem case2_Z3a {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 28 / 5 ≤ x1) (hhi : x1 ≤ 6) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases hx_600 : x ≤ 6
  · have hI := seg_int_le_cs hx1_pos le_rfl hx1x.le (by nlinarith)
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z3a_diag hlo hx1x hx_600)
  push Not at hx_600
  by_cases hx_655 : x ≤ 131 / 20
  · have hI := seg_int_le_cs hx1_pos le_rfl hx1x.le (by nlinarith)
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 hx_600.le (by linarith)) hI
      (cert_Z3a_Z3b hlo hhi hx_600.le hx_655 hx1x)
  push Not at hx_655
  by_cases hx_675 : x ≤ 27 / 4
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (1 / 2) * phi2 x1 x1 (131 / 20) + (7 / 4) * phi3 x1 x1 (131 / 20) +
        (7 / 20) * phi2 x1 (131 / 20) x := by
      rw [int_split hx1_pos (by linarith) hx_655.le]
      have i1 := seg_int_le_cs (a := x1) (b := 131 / 20) hx1_pos le_rfl (by linarith) (by nlinarith)
      have i2 := seg_int_le_c2 (a := 131 / 20) (b := x) hx1_pos (by linarith) hx_655.le (by norm_num)
        (fun v hv => HDeriv2_Z4 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 (by linarith) hx_675) hI
      (cert_Z3a_Z4a hlo hhi hx_655.le hx_675)
  · push Not at hx_675
    by_cases hx1_575 : x1 ≤ 23 / 4
    · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 28 / 5) (b1 := 23 / 4) (x_lo := 27 / 4)
        (s_max := 64 / 100) (by norm_num) hlo hx1_575 (by norm_num) hx_675.le (by norm_num)
        (abs_sin_le_of_two_pi_sub (y := 6832 / 10000) (by linarith) (by linarith) (by linarith)
          (by linarith) (by norm_num)) (by norm_num)
    · push Not at hx1_575
      by_cases hx1_590 : x1 ≤ 59 / 10
      · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 23 / 4) (b1 := 59 / 10) (x_lo := 27 / 4)
          (s_max := 51 / 100) (by norm_num) hx1_575.le hx1_590 (by norm_num) hx_675.le (by norm_num)
          (abs_sin_le_of_two_pi_sub (y := 5332 / 10000) (by linarith) (by linarith) (by linarith)
            (by linarith) (by norm_num)) (by norm_num)
      · push Not at hx1_590
        exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 59 / 10) (b1 := 6) (x_lo := 27 / 4)
          (s_max := 38 / 100) (by norm_num) hx1_590.le hhi (by norm_num) hx_675.le (by norm_num)
          (abs_sin_le_of_two_pi_sub (y := 3832 / 10000) (by linarith) (by linarith) (by linarith)
            (by linarith) (by norm_num)) (by norm_num)

private theorem case2_Z3b {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 6 ≤ x1) (hhi : x1 ≤ 131 / 20) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  by_cases hx_655 : x ≤ 131 / 20
  · have hI := seg_int_le_cs hx1_pos le_rfl hx1x.le (by nlinarith)
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 (by linarith) (by linarith)) hI
      (cert_Z3b_diag hlo hx1x hx_655)
  push Not at hx_655
  by_cases hx_675 : x ≤ 27 / 4
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (1 / 2) * phi2 x1 x1 (131 / 20) + (7 / 4) * phi3 x1 x1 (131 / 20) +
        (7 / 20) * phi2 x1 (131 / 20) x := by
      rw [int_split hx1_pos hhi hx_655.le]
      have i1 := seg_int_le_cs hx1_pos le_rfl hhi (by nlinarith)
      have i2 := seg_int_le_c2 hx1_pos hhi hx_655.le (by norm_num)
        (fun v hv => HDeriv2_Z4 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_38 (by linarith) hx_675) hI
      (cert_Z3b_Z4a hlo hhi hx_655.le hx_675 hx1x)
  push Not at hx_675
  by_cases hx_691 : x ≤ 691 / 100
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (1 / 2) * phi2 x1 x1 (131 / 20) + (7 / 4) * phi3 x1 x1 (131 / 20) +
        (7 / 20) * phi2 x1 (131 / 20) x := by
      rw [int_split hx1_pos hhi (by linarith)]
      have i1 := seg_int_le_cs (a := x1) (b := 131 / 20) hx1_pos le_rfl hhi (by nlinarith)
      have i2 := seg_int_le_c2 (a := 131 / 20) (b := x) hx1_pos hhi (by linarith) (by norm_num)
        (fun v hv => HDeriv2_Z4 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z3b_Z4b hlo hhi hx_675.le hx_691)
  push Not at hx_691
  by_cases hx_847 : x ≤ 847 / 100
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (1 / 2) * phi2 x1 x1 (131 / 20) + (7 / 4) * phi3 x1 x1 (131 / 20) +
        (7 / 20) * phi2 x1 (131 / 20) (691 / 100) := by
      rw [int_split hx1_pos hhi (by linarith),
          int_split (by norm_num) (by norm_num : (131 / 20 : ℝ) ≤ 691 / 100) hx_691.le]
      have i1 := seg_int_le_cs hx1_pos le_rfl hhi (by nlinarith)
      have i2 := seg_int_le_c2 hx1_pos hhi (by norm_num) (by norm_num) (fun v hv => HDeriv2_Z4 hv.1 hv.2)
      have i3 := seg_int_le_zero hx1_pos (by linarith) hx_691.le
        (fun v hv => HDeriv2_Z5 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2, i3]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z3b_Z5 hlo hhi hx_691.le hx_847)
  · push Not at hx_847
    exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 6) (b1 := 131 / 20) (x_lo := 847 / 100)
      (s_max := 1) (by norm_num) hlo hhi (by norm_num) hx_847.le (by norm_num)
      (Real.abs_sin_le_one x1) (by norm_num)

private theorem case2_Z4 {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 131 / 20 ≤ x1) (hhi : x1 ≤ 691 / 100) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  by_cases hx_691 : x ≤ 691 / 100
  · have hI := seg_int_le_c2 hx1_pos le_rfl hx1x.le (by norm_num)
      (fun v hv => HDeriv2_Z4 (le_trans (by nlinarith) hv.1) (le_trans hv.2 (by nlinarith)))
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z4_diag hlo hx1x hx_691)
  push Not at hx_691
  by_cases hx_847 : x ≤ 847 / 100
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤ (7 / 20) * phi2 x1 x1 (691 / 100) := by
      rw [int_split hx1_pos hhi hx_691.le]
      have i1 := seg_int_le_c2 hx1_pos le_rfl hhi (by norm_num)
        (fun v hv => HDeriv2_Z4 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_zero hx1_pos hhi hx_691.le
        (fun v hv => HDeriv2_Z5 hv.1 (le_trans hv.2 (by nlinarith)))
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z4_Z5 hlo hhi hx_691.le hx_847 hx1x)
  · push Not at hx_847
    exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 131 / 20) (b1 := 691 / 100) (x_lo := 847 / 100)
      (s_max := 1) (by norm_num) hlo hhi (by norm_num) hx_847.le (by norm_num)
      (Real.abs_sin_le_one x1) (by norm_num)

private theorem case2_Z5 {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x)
    (hlo : 691 / 100 ≤ x1) (hhi : x1 ≤ 847 / 100) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  by_cases hx_847 : x ≤ 847 / 100
  · have hI := seg_int_le_zero hx1_pos le_rfl hx1x.le
      (fun v hv => HDeriv2_Z5 (le_trans (by nlinarith) hv.1) (le_trans hv.2 (by nlinarith)))
    have hdiff : 0 < x ^ 2 - x1 ^ 2 := by nlinarith
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (by rw [mul_zero]; positivity)
  push Not at hx_847
  by_cases hx_975 : x ≤ 39 / 4
  · have hI : ∫ v in x1 ^ 2..x ^ 2, (v - x1 ^ 2) * HDeriv2 v ≤
        (1 / 2) * phi2 x1 (847 / 100) x + (7 / 4) * phi3 x1 (847 / 100) x := by
      rw [int_split hx1_pos hhi hx_847.le]
      have i1 := seg_int_le_zero hx1_pos le_rfl hhi (fun v hv => HDeriv2_Z5 (le_trans (by nlinarith) hv.1) hv.2)
      have i2 := seg_int_le_cs hx1_pos hhi hx_847.le (by norm_num)
      linarith only [i1, i2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI
      (cert_Z5_Z6 hlo hhi hx_847.le hx_975 hx1x)
  · push Not at hx_975
    have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
    by_cases hx1_770 : x1 ≤ 77 / 10
    · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 691 / 100) (b1 := 77 / 10) (x_lo := 39 / 4)
        (s_max := 1) (by norm_num) hlo hx1_770 (by norm_num) hx_975.le (by norm_num)
        (Real.abs_sin_le_one x1) (by norm_num)
    · push Not at hx1_770
      by_cases hx1_810 : x1 ≤ 81 / 10
      · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 77 / 10) (b1 := 81 / 10) (x_lo := 39 / 4)
          (s_max := 1) (by norm_num) hx1_770.le hx1_810 (by norm_num) hx_975.le (by norm_num)
          (Real.abs_sin_le_one x1) (by norm_num)
      · push Not at hx1_810
        by_cases hx1_830 : x1 ≤ 83 / 10
        · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 81 / 10) (b1 := 83 / 10) (x_lo := 39 / 4)
            (s_max := 1) (by norm_num) hx1_810.le hx1_830 (by norm_num) hx_975.le (by norm_num)
            (Real.abs_sin_le_one x1) (by norm_num)
        · push Not at hx1_830
          exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 83 / 10) (b1 := 847 / 100) (x_lo := 39 / 4)
            (s_max := 91 / 100) (by norm_num) hx1_830.le hhi (by norm_num) hx_975.le (by norm_num)
            (abs_sin_le_of_three_pi_sub (y := 11248 / 10000) (by linarith) (by linarith)
              (by linarith) (by linarith) (by norm_num)) (by norm_num)

private theorem case2_Z6 {u x1 x : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hu_x1 : u < x1) (hx1x : x1 < x) (hx_ge : 83 / 20 ≤ x) (hlo : 847 / 100 ≤ x1) :
    Hww (x1 ^ 2) (x ^ 2) < Hww (u ^ 2) (x ^ 2) := by
  have hx1_pos : 0 < x1 := by linarith
  have hx_pos : 0 < x := lt_trans hx1_pos hx1x
  by_cases hratio : x ≤ (117 / 100 : ℝ) * x1
  · have hI := seg_int_le_cs hx1_pos le_rfl hx1x.le (by nlinarith)
    have hB : x ^ 4 * ((1 / 2) * phi2 x1 x1 x + (7 / 4) * phi3 x1 x1 x) <
        (33 / 100) * (x ^ 2 - x1 ^ 2) ^ 2 := by
      have hid : x ^ 4 * ((1 / 2) * phi2 x1 x1 x + (7 / 4) * phi3 x1 x1 x) =
          (x ^ 2 - x1 ^ 2) ^ 2 * (x ^ 2 / (2 * x1 * (x + x1)) + 7 / (8 * x1 ^ 2)) := by
        unfold phi2 phi3
        field_simp [hx1_pos.ne', hx_pos.ne', (by linarith : x + x1 ≠ 0)]
        ring
      rw [hid, mul_comm (33 / 100 : ℝ)]
      refine mul_lt_mul_of_pos_left ?_ (sq_pos_of_pos (by nlinarith))
      have h1 : x ^ 2 / (2 * x1 * (x + x1)) ≤ 3155 / 10000 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hx1_pos, hx1x, hratio]
      have h2 : 7 / (8 * x1 ^ 2) ≤ 125 / 10000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hlo]
      linarith only [h1, h2]
    exact Hww_lt_of_taylor hu0 hu hx1_pos hx1x hx_ge (lower_bound_33 hx_ge) hI hB
  · push Not at hratio
    refine Hww_lt_of_direct hu0 hu hu_x1 hx1x (s := 1) (by norm_num) (Real.abs_sin_le_one x1) ?_
    have hr2 : x1 ^ 2 / x ^ 2 ≤ (100 / 117 : ℝ) ^ 2 := by
      rw [div_le_iff₀ (sq_pos_of_pos hx_pos)]; nlinarith only [hx1_pos, hratio]
    have h1m : (1 - (100 / 117 : ℝ) ^ 2) ≤ 1 - x1 ^ 2 / x ^ 2 := by linarith
    have h1m_pos : (0 : ℝ) < 1 - (100 / 117 : ℝ) ^ 2 := by norm_num
    have ht1 : (1 ^ 2 / x1 ^ 2) / (1 - x1 ^ 2 / x ^ 2) ^ 2 ≤
        (1 / (847 / 100 : ℝ) ^ 2) / (1 - (100 / 117 : ℝ) ^ 2) ^ 2 := by
      have ha : (1 : ℝ) ^ 2 / x1 ^ 2 ≤ 1 / (847 / 100 : ℝ) ^ 2 := by
        rw [one_pow]
        exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by nlinarith only [hlo])
      have hb : (1 - (100 / 117 : ℝ) ^ 2) ^ 2 ≤ (1 - x1 ^ 2 / x ^ 2) ^ 2 := by nlinarith only [h1m, h1m_pos]
      exact le_trans (div_le_div_of_nonneg_right ha (by positivity))
        (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos h1m_pos) hb)
    have ht2 : (x1 ^ 2 / (x ^ 2 - x1 ^ 2)) / (2 * x) ≤
        ((100 / 117 : ℝ) ^ 2 / (1 - (100 / 117 : ℝ) ^ 2)) / (2 * (117 / 100 * (847 / 100))) := by
      have hfrac : x1 ^ 2 / (x ^ 2 - x1 ^ 2) ≤ (100 / 117 : ℝ) ^ 2 / (1 - (100 / 117 : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by nlinarith only [hx1_pos, hx1x]) h1m_pos]
        nlinarith only [hx1_pos, hratio]
      exact le_trans (div_le_div_of_nonneg_right hfrac (by positivity))
        (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith only [hlo, hratio]))
    have hc1 : (1 / (847 / 100 : ℝ) ^ 2) / (1 - (100 / 117 : ℝ) ^ 2) ^ 2 < 20 / 100 := by norm_num
    have hc2 : ((100 / 117 : ℝ) ^ 2 / (1 - (100 / 117 : ℝ) ^ 2)) / (2 * (117 / 100 * (847 / 100))) <
        15 / 100 := by norm_num
    linarith only [ht1, ht2, hc1, hc2]

/-- Master Confluent Comparison: `Hww w1 w < Hww (u²) w` for ALL `0 < u < π/2`, `u² < w1 < w`. -/
theorem Hww_lt_of_u_sq {u w1 w : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hw1 : u ^ 2 < w1) (hw1w : w1 < w) :
    Hww w1 w < Hww (u ^ 2) w := by
  have hw1_pos : 0 < w1 := lt_trans (sq_pos_of_pos hu0) hw1
  have hw_pos : 0 < w := lt_trans hw1_pos hw1w
  set x1 := Real.sqrt w1
  set x := Real.sqrt w
  have hx1_pos : 0 < x1 := Real.sqrt_pos.mpr hw1_pos
  have hx_pos : 0 < x := Real.sqrt_pos.mpr hw_pos
  have hx1_sq : x1 ^ 2 = w1 := Real.sq_sqrt hw1_pos.le
  have hx_sq : x ^ 2 = w := Real.sq_sqrt hw_pos.le
  have hu_x1 : u < x1 := by nlinarith
  have hx1x : x1 < x := by nlinarith
  by_cases hcase0 : x ≤ 83 / 20
  · exact Hww_strictAnti_case0 (sq_pos_of_pos hu0) hw1 hw1w hcase0
  push Not at hcase0
  by_cases hcase1 : x1 ≤ 5 / 2
  · exact Hww_strictAnti_case1 (sq_pos_of_pos hu0) hw1 (by rw [← hx1_sq]; nlinarith) hcase0.le
  push Not at hcase1
  rw [← hx1_sq, ← hx_sq]
  have hpi_gt : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  by_cases hx1_295 : x1 ≤ 59 / 20
  · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 5 / 2) (b1 := 59 / 20) (x_lo := 83 / 20)
      (s_max := 65 / 100) (by norm_num) hcase1.le hx1_295 (by norm_num) hcase0.le (by norm_num)
      (le_trans (abs_sin_le_abs_sub_pi x1) (abs_le.mpr ⟨by linarith, by linarith⟩)) (by norm_num)
  push Not at hx1_295
  by_cases hx1_340 : x1 ≤ 17 / 5
  · exact direct_box_ok hu0 hu hu_x1 hx1x (a1 := 59 / 20) (b1 := 17 / 5) (x_lo := 83 / 20)
      (s_max := 26 / 100) (by norm_num) hx1_295.le hx1_340 (by norm_num) hcase0.le (by norm_num)
      (le_trans (abs_sin_le_abs_sub_pi x1) (abs_le.mpr ⟨by linarith, by linarith⟩)) (by norm_num)
  push Not at hx1_340
  by_cases hx1_366 : x1 ≤ 183 / 50
  · exact case2_Z0 hu0 hu hu_x1 hx1x hcase0.le hx1_340.le hx1_366
  push Not at hx1_366
  by_cases hx1_522 : x1 ≤ 261 / 50
  · exact case2_Z1 hu0 hu hu_x1 hx1x hcase0.le hx1_366.le hx1_522
  push Not at hx1_522
  by_cases hx1_560 : x1 ≤ 28 / 5
  · exact case2_Z2 hu0 hu hu_x1 hx1x hcase0.le hx1_522.le hx1_560
  push Not at hx1_560
  by_cases hx1_600 : x1 ≤ 6
  · exact case2_Z3a hu0 hu hu_x1 hx1x hcase0.le hx1_560.le hx1_600
  push Not at hx1_600
  by_cases hx1_655 : x1 ≤ 131 / 20
  · exact case2_Z3b hu0 hu hu_x1 hx1x hcase0.le hx1_600.le hx1_655
  push Not at hx1_655
  by_cases hx1_691 : x1 ≤ 691 / 100
  · exact case2_Z4 hu0 hu hu_x1 hx1x hcase0.le hx1_655.le hx1_691
  push Not at hx1_691
  by_cases hx1_847 : x1 ≤ 847 / 100
  · exact case2_Z5 hu0 hu hu_x1 hx1x hcase0.le hx1_691.le hx1_847
  push Not at hx1_847
  exact case2_Z6 hu0 hu hu_x1 hx1x hcase0.le hx1_847.le

/-! ### 9. Strict Anti-Monotonicity of `H2dd` & Theorem 6 (`odd_critical_9x9_no_ESE`) -/

theorem H2dd_strictAnti {u w1 w2 w3 : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hw1 : u ^ 2 < w1) (hw12 : w1 < w2) (hw23 : w2 < w3) :
    H2dd (u ^ 2) w1 w3 < H2dd (u ^ 2) w1 w2 := by
  have hanti : StrictAntiOn (H2dd (u ^ 2) w1) (Set.Icc w2 w3) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc w2 w3) ?_ ?_
    · intro w hw
      exact (hasDerivAt_H2dd (sq_pos_of_pos hu0) hw1 (lt_of_lt_of_le hw12 hw.1)).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hw1w : w1 < w := lt_trans hw12 hw.1
      rw [(hasDerivAt_H2dd (sq_pos_of_pos hu0) hw1 hw1w).deriv]
      exact div_neg_of_neg_of_pos (sub_neg.mpr (Hww_lt_of_u_sq hu0 hu hw1 hw1w)) (sub_pos.mpr hw1)
  exact hanti (Set.left_mem_Icc.mpr hw23.le) (Set.right_mem_Icc.mpr hw23.le) hw23

private theorem vand9_alg {B C D : ℝ} (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hB1 : B - 1 ≠ 0) (hC1 : C - 1 ≠ 0) (hD1 : D - 1 ≠ 0)
    (hCB : C - B ≠ 0) (hDB : D - B ≠ 0) (hDC : D - C ≠ 0) :
    1 / (B * C * D) - 1 / ((B - 1) * (C - 1) * (D - 1)) +
    1 / (B * (B - 1) * (C - B) * (D - B)) -
    1 / (C * (C - 1) * (C - B) * (D - C)) +
    1 / (D * (D - 1) * (D - B) * (D - C)) = 0 := by
  field_simp [hB, hC, hD, hB1, hC1, hD1, hCB, hDB, hDC]
  ring

private theorem num9_alg {B C D h0 h1 h2 h3 : ℝ}
    (hB1 : B - 1 ≠ 0) (hC1 : C - 1 ≠ 0) (hD1 : D - 1 ≠ 0)
    (hCB : C - B ≠ 0) (hDB : D - B ≠ 0) (hDC : D - C ≠ 0) :
    h0 / ((B - 1) * (C - 1) * (D - 1)) -
    h1 / ((B - 1) * (C - B) * (D - B)) +
    h2 / ((C - 1) * (C - B) * (D - C)) -
    h3 / ((D - 1) * (D - B) * (D - C)) =
    1 / (D - C) * (((h0 - h1) / (B - 1) - (h0 - h2) / (C - 1)) / (C - B) -
                   ((h0 - h1) / (B - 1) - (h0 - h3) / (D - 1)) / (D - B)) := by
  field_simp [hB1, hC1, hD1, hCB, hDB, hDC]
  ring

/-- **Theorem 6 (Critical `9 × 9` No-ESE Theorem):**
For EVERY `9 × 9` symmetric PST Jacobi chain `{0, ±1, ±b, ±c, ±d}` with alternating parity
(`b` even, `c` odd, `d` even, `1 < b < c < d`), the return amplitude `amp9 1 b c d t` is
strictly positive on `[0, π)` — hence NO `9 × 9` symmetric PST chain with minimal gap `λ₁ = 1`
exhibits Early State Exclusion. Combined with Theorem 7 (`11 × 11` sharp threshold `M* = 12`),
this establishes the exact odd rupture dimension `N_crit^odd = 11`. -/
theorem odd_critical_9x9_no_ESE {b c d : ℕ}
    (h1b : 1 < b) (hbc : b < c) (hcd : c < d)
    (hb_even : Even b) (hc_odd : Odd c) (hd_even : Even d) :
    ∀ t : ℝ, 0 ≤ t → t < Real.pi → 0 < amp9 1 (b : ℝ) (c : ℝ) (d : ℝ) t := by
  intro t ht0 htpi
  set lb : ℝ := (b : ℝ)
  set lc : ℝ := (c : ℝ)
  set ld : ℝ := (d : ℝ)
  have h1b' : (1 : ℝ) < lb := by simp only [lb]; exact_mod_cast h1b
  have hbc' : lb < lc := by simp only [lb, lc]; exact_mod_cast hbc
  have hcd' : lc < ld := by simp only [lc, ld]; exact_mod_cast hcd
  have hb0 : 0 < lb := by linarith
  have hc0 : 0 < lc := by linarith
  have hd0 : 0 < ld := by linarith
  set B : ℝ := lb ^ 2
  set C : ℝ := lc ^ 2
  set D : ℝ := ld ^ 2
  have hB0 : 0 < B := sq_pos_of_pos hb0
  have hC0 : 0 < C := sq_pos_of_pos hc0
  have hD0 : 0 < D := sq_pos_of_pos hd0
  have hB1 : 0 < B - 1 := by simp only [B]; nlinarith
  have hC1 : 0 < C - 1 := by simp only [C]; nlinarith
  have hD1 : 0 < D - 1 := by simp only [D]; nlinarith
  have hCB : 0 < C - B := by simp only [B, C]; nlinarith
  have hDB : 0 < D - B := by simp only [B, D]; nlinarith
  have hDC : 0 < D - C := by simp only [C, D]; nlinarith
  set w0 : ℝ := 1 / (1 ^ 2 * lb ^ 2 * lc ^ 2 * ld ^ 2)
  set w1 : ℝ := 1 / (1 ^ 2 * (lb ^ 2 - 1 ^ 2) * (lc ^ 2 - 1 ^ 2) * (ld ^ 2 - 1 ^ 2))
  set w2 : ℝ := 1 / (lb ^ 2 * (lb ^ 2 - 1 ^ 2) * (lc ^ 2 - lb ^ 2) * (ld ^ 2 - lb ^ 2))
  set w3 : ℝ := 1 / (lc ^ 2 * (lc ^ 2 - 1 ^ 2) * (lc ^ 2 - lb ^ 2) * (ld ^ 2 - lc ^ 2))
  set w4 : ℝ := 1 / (ld ^ 2 * (ld ^ 2 - 1 ^ 2) * (ld ^ 2 - lb ^ 2) * (ld ^ 2 - lc ^ 2))
  have hw0_eq : w0 = 1 / (B * C * D) := by simp only [w0, B, C, D]; ring
  have hw1_eq : w1 = 1 / ((B - 1) * (C - 1) * (D - 1)) := by simp only [w1, B, C, D]; ring
  have hw2_eq : w2 = 1 / (B * (B - 1) * (C - B) * (D - B)) := by simp only [w2, B, C, D]; ring
  have hw3_eq : w3 = 1 / (C * (C - 1) * (C - B) * (D - C)) := by simp only [w3, B, C, D]; ring
  have hw4_eq : w4 = 1 / (D * (D - 1) * (D - B) * (D - C)) := by simp only [w4, B, C, D]; ring
  have hw0 : 0 < w0 := by rw [hw0_eq]; positivity
  have hw1 : 0 < w1 := by rw [hw1_eq]; positivity
  have hw2 : 0 < w2 := by rw [hw2_eq]; positivity
  have hw3 : 0 < w3 := by rw [hw3_eq]; positivity
  have hw4 : 0 < w4 := by rw [hw4_eq]; positivity
  have hden : 0 < w0 + w1 + w2 + w3 + w4 := by linarith
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · unfold amp9; dsimp only
    simp only [mul_zero, Real.cos_zero, mul_one]
    change 0 < (w0 + w1 + w2 + w3 + w4) / (w0 + w1 + w2 + w3 + w4)
    rw [div_self hden.ne']; norm_num
  set u : ℝ := (Real.pi - t) / 2
  have hu0 : 0 < u := by simp only [u]; linarith
  have hu_lt : u < Real.pi / 2 := by simp only [u]; linarith
  have ht_eq : t = Real.pi - 2 * u := by simp only [u]; ring
  have hcos1 : Real.cos (1 * t) = -Real.cos (2 * u) := by
    rw [one_mul, ht_eq, Real.cos_pi_sub]
  have hcosb : Real.cos (lb * t) = Real.cos (2 * lb * u) := by
    obtain ⟨kb, rfl⟩ := hb_even
    have harg : ((kb + kb : ℕ) : ℝ) * (Real.pi - 2 * u) = -(2 * ((kb + kb : ℕ) : ℝ) * u) + (kb : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [ht_eq]; simp only [lb]; rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have hcosc : Real.cos (lc * t) = -Real.cos (2 * lc * u) := by
    obtain ⟨kc, rfl⟩ := hc_odd
    have harg : ((2 * kc + 1 : ℕ) : ℝ) * (Real.pi - 2 * u) =
        (Real.pi - 2 * ((2 * kc + 1 : ℕ) : ℝ) * u) + (kc : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [ht_eq]; simp only [lc]; rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_pi_sub]
  have hcosd : Real.cos (ld * t) = Real.cos (2 * ld * u) := by
    obtain ⟨kd, rfl⟩ := hd_even
    have harg : ((kd + kd : ℕ) : ℝ) * (Real.pi - 2 * u) = -(2 * ((kd + kd : ℕ) : ℝ) * u) + (kd : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [ht_eq]; simp only [ld]; rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have hvand : w0 - w1 + w2 - w3 + w4 = 0 := by
    rw [hw0_eq, hw1_eq, hw2_eq, hw3_eq, hw4_eq]
    exact vand9_alg hB0.ne' hC0.ne' hD0.ne' hB1.ne' hC1.ne' hD1.ne' hCB.ne' hDB.ne' hDC.ne'
  set x0 := u ^ 2
  set x1 := (lb * u) ^ 2
  set x2 := (lc * u) ^ 2
  set x3 := (ld * u) ^ 2
  have hx0_pos : 0 < x0 := sq_pos_of_pos hu0
  have hx01 : x0 < x1 := by
    have : x1 - x0 = (B - 1) * x0 := by simp only [x0, x1, B]; ring
    nlinarith only [this, hB1, hx0_pos]
  have hx12 : x1 < x2 := by
    have : x2 - x1 = (C - B) * x0 := by simp only [x0, x1, x2, B, C]; ring
    nlinarith only [this, hCB, hx0_pos]
  have hx23 : x2 < x3 := by
    have : x3 - x2 = (D - C) * x0 := by simp only [x0, x2, x3, C, D]; ring
    nlinarith only [this, hDC, hx0_pos]
  have hH0 : 1 - Real.cos (2 * u) = 2 * x0 * H x0 := by
    simp only [H, hx0_pos.ne', ↓reduceIte, x0, Real.sqrt_sq hu0.le]; field_simp [hu0.ne']
  have hH1 : 1 - Real.cos (2 * lb * u) = 2 * x1 * H x1 := by
    have hpos : 0 < lb * u := mul_pos hb0 hu0
    simp only [H, (sq_pos_of_pos hpos).ne', ↓reduceIte, x1, Real.sqrt_sq hpos.le]
    rw [show 2 * (lb * u) = 2 * lb * u by ring]; field_simp [hpos.ne']
  have hH2 : 1 - Real.cos (2 * lc * u) = 2 * x2 * H x2 := by
    have hpos : 0 < lc * u := mul_pos hc0 hu0
    simp only [H, (sq_pos_of_pos hpos).ne', ↓reduceIte, x2, Real.sqrt_sq hpos.le]
    rw [show 2 * (lc * u) = 2 * lc * u by ring]; field_simp [hpos.ne']
  have hH3 : 1 - Real.cos (2 * ld * u) = 2 * x3 * H x3 := by
    have hpos : 0 < ld * u := mul_pos hd0 hu0
    simp only [H, (sq_pos_of_pos hpos).ne', ↓reduceIte, x3, Real.sqrt_sq hpos.le]
    rw [show 2 * (ld * u) = 2 * ld * u by ring]; field_simp [hpos.ne']
  have hdd := H2dd_strictAnti hu0 hu_lt hx01 hx12 hx23
  change 0 < (w0 + w1 * Real.cos (1 * t) + w2 * Real.cos (lb * t) +
    w3 * Real.cos (lc * t) + w4 * Real.cos (ld * t)) / (w0 + w1 + w2 + w3 + w4)
  refine div_pos ?_ hden
  rw [hcos1, hcosb, hcosc, hcosd]
  have hstep : w0 + w1 * -Real.cos (2 * u) + w2 * Real.cos (2 * lb * u) +
      w3 * -Real.cos (2 * lc * u) + w4 * Real.cos (2 * ld * u) =
      w1 * (1 - Real.cos (2 * u)) - w2 * (1 - Real.cos (2 * lb * u)) +
      w3 * (1 - Real.cos (2 * lc * u)) - w4 * (1 - Real.cos (2 * ld * u)) := by linarith only [hvand]
  rw [hstep, hH0, hH1, hH2, hH3, hw1_eq, hw2_eq, hw3_eq, hw4_eq]
  have hx1_eq : x1 = B * x0 := by simp only [x1, B, x0]; ring
  have hx2_eq : x2 = C * x0 := by simp only [x2, C, x0]; ring
  have hx3_eq : x3 = D * x0 := by simp only [x3, D, x0]; ring
  have hred :
      1 / ((B - 1) * (C - 1) * (D - 1)) * (2 * x0 * H x0) -
      1 / (B * (B - 1) * (C - B) * (D - B)) * (2 * x1 * H x1) +
      1 / (C * (C - 1) * (C - B) * (D - C)) * (2 * x2 * H x2) -
      1 / (D * (D - 1) * (D - B) * (D - C)) * (2 * x3 * H x3) =
      2 * x0 * (H x0 / ((B - 1) * (C - 1) * (D - 1)) -
                H x1 / ((B - 1) * (C - B) * (D - B)) +
                H x2 / ((C - 1) * (C - B) * (D - C)) -
                H x3 / ((D - 1) * (D - B) * (D - C))) := by
    rw [hx1_eq, hx2_eq, hx3_eq]
    field_simp [hB0.ne', hC0.ne', hD0.ne', hB1.ne', hC1.ne', hD1.ne', hCB.ne', hDB.ne', hDC.ne']
  rw [hred, num9_alg hB1.ne' hC1.ne' hD1.ne' hCB.ne' hDB.ne' hDC.ne']
  have hdd_scale :
      ((H x0 - H x1) / (B - 1) - (H x0 - H x2) / (C - 1)) / (C - B) -
      ((H x0 - H x1) / (B - 1) - (H x0 - H x3) / (D - 1)) / (D - B) =
      x0 ^ 2 * (H2dd x0 x1 x2 - H2dd x0 x1 x3) := by
    unfold H2dd
    rw [hx1_eq, hx2_eq, hx3_eq]
    have hx0_ne : x0 ≠ 0 := hx0_pos.ne'
    have h10 : B * x0 - x0 = (B - 1) * x0 := by ring
    have h20 : C * x0 - x0 = (C - 1) * x0 := by ring
    have h30 : D * x0 - x0 = (D - 1) * x0 := by ring
    have h21 : C * x0 - B * x0 = (C - B) * x0 := by ring
    have h31 : D * x0 - B * x0 = (D - B) * x0 := by ring
    rw [h10, h20, h30, h21, h31]
    field_simp [hx0_ne, hB1.ne', hC1.ne', hD1.ne', hCB.ne', hDB.ne']
  rw [hdd_scale]
  exact mul_pos (by positivity) (mul_pos (div_pos one_pos hDC) (mul_pos (sq_pos_of_pos hx0_pos) (sub_pos.mpr hdd)))

end SpectralEclipse
