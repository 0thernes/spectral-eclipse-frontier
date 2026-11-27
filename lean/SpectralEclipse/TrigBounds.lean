/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Analytic Trigonometric, Positive-Kernel Integral, and Bernstein Positivity Certificates

Establishes all elementary analytic lemmas powering the forward no-ESE theorems for `4 × 4`,
`5 × 5`, `6 × 6`, `7 × 7` (Conjecture 4.1), and `9 × 9`, plus the Taylor bounds for the
Discrete Fourier Coset-Averaging converse of Conjecture 4.1:
  - Alternating Maclaurin bounds `taylorCos (2*m + 2) θ ≤ cos θ ≤ taylorCos (2*m + 1) θ` (`θ ≥ 0`).
  - Jordan bounds `2/π ≤ He(u²)`, `4/π² ≤ H(u²)`, and `|sin(q u)| < q sin u` (`q > 1`, `u ∈ (0, π/2)`).
  - Exact positive-kernel cosine-transform identities for `He''(x²)`, `H''(x²)`, and `-H'''(x²)`.
  - Single-interval exact rational Bernstein certificates proving:
      * `He''(x²) > 0` on `(0, 11/2]` (`6 × 6`),
      * `H''(x²) > 0` on `(0, 33/10]` (`7 × 7`),
      * `H'''(x²) < 0` on `(0, 83/20]` (`9 × 9`).
  - Square-root-free algebraic tail bounds proving `He(u²) - He(x²) + (x² - u²) He'(x²) > 0`
    (`x ≥ 11/2`) and `H(u²) - H(x²) + (x² - u²) H'(x²) > 0` (`x ≥ 33/10`), hence global strict
    monotonicity of the divided-difference slope functions `G_u` and `Ge_u`.
-/

@[expose] public section

open scoped BigOperators
open Finset intervalIntegral

namespace SpectralEclipse

/-! ### 1. Alternating Maclaurin Bounds for `cos` and `sin` on `[0, ∞)` -/

/-- `k`-term Maclaurin polynomial of `cos θ`. -/
noncomputable def taylorCos (k : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * θ ^ (2 * j) / ((2 * j).factorial : ℝ)

/-- `k`-term Maclaurin polynomial of `sin θ`. -/
noncomputable def taylorSin (k : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * θ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)

theorem taylorCos_zero_at_zero (k : ℕ) (hk : 1 ≤ k) : taylorCos k 0 = 1 := by
  cases k with
  | zero => omega
  | succ m =>
    rw [taylorCos, Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    have hzero : ∑ j ∈ Finset.range m,
        (-1 : ℝ) ^ (j + 1) * (0 : ℝ) ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [zero_pow (by omega : 2 * (j + 1) ≠ 0)]
      ring
    rw [hzero, zero_add]

theorem taylorSin_zero_at_zero (k : ℕ) : taylorSin k 0 = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [zero_pow (by omega : 2 * j + 1 ≠ 0)]
  ring

theorem hasDerivAt_taylorSin (k : ℕ) (θ : ℝ) :
    HasDerivAt (taylorSin k) (taylorCos k θ) θ := by
  unfold taylorSin taylorCos
  have hterm : ∀ j ∈ Finset.range k,
      HasDerivAt (fun x : ℝ => (-1 : ℝ) ^ j * x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
        ((-1 : ℝ) ^ j * θ ^ (2 * j) / ((2 * j).factorial : ℝ)) θ := by
    intro j _
    have hp : HasDerivAt (fun x : ℝ => x ^ (2 * j + 1)) (((2 * j + 1 : ℕ) : ℝ) * θ ^ (2 * j)) θ := by
      simpa using hasDerivAt_pow (2 * j + 1) θ
    have h1 := (hp.const_mul ((-1 : ℝ) ^ j)).div_const (((2 * j + 1).factorial : ℝ))
    refine h1.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have hne : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfac : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
    field_simp [hne, hfac]
  exact HasDerivAt.fun_sum hterm

theorem hasDerivAt_taylorCos_succ (k : ℕ) (θ : ℝ) :
    HasDerivAt (taylorCos (k + 1)) (-taylorSin k θ) θ := by
  have hfun : taylorCos (k + 1) =
      fun x : ℝ => (∑ j ∈ Finset.range k,
        (-1 : ℝ) ^ (j + 1) * x ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ)) + 1 := by
    funext x
    rw [taylorCos, Finset.sum_range_succ']
    simp
  rw [hfun]
  have hterm : ∀ j ∈ Finset.range k,
      HasDerivAt (fun x : ℝ => (-1 : ℝ) ^ (j + 1) * x ^ (2 * (j + 1)) / ((2 * (j + 1)).factorial : ℝ))
        (-((-1 : ℝ) ^ j * θ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))) θ := by
    intro j _
    have hp : HasDerivAt (fun x : ℝ => x ^ (2 * (j + 1)))
        (((2 * (j + 1) : ℕ) : ℝ) * θ ^ (2 * j + 1)) θ := by
      simpa [Nat.mul_add] using hasDerivAt_pow (2 * (j + 1)) θ
    have h1 := (hp.const_mul ((-1 : ℝ) ^ (j + 1))).div_const (((2 * (j + 1)).factorial : ℝ))
    refine h1.congr_deriv ?_
    have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [h2, Nat.factorial_succ, pow_succ]
    push_cast
    have hne : ((2 * j + 1 : ℝ) + 1) ≠ 0 := by positivity
    have hfac : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp [hne, hfac]
  have h2 := (HasDerivAt.fun_sum hterm).add_const (1 : ℝ)
  refine h2.congr_deriv ?_
  unfold taylorSin
  rw [Finset.sum_neg_distrib]

private theorem nonneg_of_deriv_nonneg {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 ≤ x → 0 ≤ f' x) (h0 : 0 ≤ f 0) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ f θ := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hf x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hf x (interior_subset hx)).deriv]
      exact hf' x (interior_subset hx)
  exact le_trans h0 (hmono (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hθ hθ)

/-- Simultaneous alternating Maclaurin bounds for `cos` and `sin` on `[0, ∞)` for every order `m`. -/
theorem taylor_trig_bounds (m : ℕ) :
    (∀ θ, 0 ≤ θ → Real.cos θ ≤ taylorCos (2 * m + 1) θ) ∧
    (∀ θ, 0 ≤ θ → Real.sin θ ≤ taylorSin (2 * m + 1) θ) ∧
    (∀ θ, 0 ≤ θ → taylorCos (2 * m + 2) θ ≤ Real.cos θ) ∧
    (∀ θ, 0 ≤ θ → taylorSin (2 * m + 2) θ ≤ Real.sin θ) := by
  induction m with
  | zero =>
    have h1 : ∀ θ, 0 ≤ θ → Real.cos θ ≤ taylorCos 1 θ := by
      intro θ _
      simp [taylorCos, Real.cos_le_one]
    have h2 : ∀ θ, 0 ≤ θ → Real.sin θ ≤ taylorSin 1 θ := by
      intro θ hθ
      have := nonneg_of_deriv_nonneg
        (f := fun x => taylorSin 1 x - Real.sin x)
        (f' := fun x => taylorCos 1 x - Real.cos x)
        (fun x _ => (hasDerivAt_taylorSin 1 x).sub (Real.hasDerivAt_sin x))
        (fun x hx => sub_nonneg.mpr (h1 x hx))
        (by simp [taylorSin_zero_at_zero]) hθ
      linarith
    have h3 : ∀ θ, 0 ≤ θ → taylorCos 2 θ ≤ Real.cos θ := by
      intro θ hθ
      have := nonneg_of_deriv_nonneg
        (f := fun x => Real.cos x - taylorCos 2 x)
        (f' := fun x => taylorSin 1 x - Real.sin x)
        (fun x _ => by
          have hd := (Real.hasDerivAt_cos x).sub (hasDerivAt_taylorCos_succ 1 x)
          convert hd using 1; ring)
        (fun x hx => sub_nonneg.mpr (h2 x hx))
        (by simp [taylorCos_zero_at_zero 2 (by omega)]) hθ
      linarith
    have h4 : ∀ θ, 0 ≤ θ → taylorSin 2 θ ≤ Real.sin θ := by
      intro θ hθ
      have := nonneg_of_deriv_nonneg
        (f := fun x => Real.sin x - taylorSin 2 x)
        (f' := fun x => Real.cos x - taylorCos 2 x)
        (fun x _ => (Real.hasDerivAt_sin x).sub (hasDerivAt_taylorSin 2 x))
        (fun x hx => sub_nonneg.mpr (h3 x hx))
        (by simp [taylorSin_zero_at_zero]) hθ
      linarith
    exact ⟨h1, h2, h3, h4⟩
  | succ m ih =>
    rcases ih with ⟨_, _, _, ih4⟩
    have h1 : ∀ θ, 0 ≤ θ → Real.cos θ ≤ taylorCos (2 * (m + 1) + 1) θ := by
      intro θ hθ
      have hidx : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by omega
      rw [hidx]
      have := nonneg_of_deriv_nonneg
        (f := fun x => taylorCos ((2 * m + 2) + 1) x - Real.cos x)
        (f' := fun x => Real.sin x - taylorSin (2 * m + 2) x)
        (fun x _ => by
          have hd := (hasDerivAt_taylorCos_succ (2 * m + 2) x).sub (Real.hasDerivAt_cos x)
          convert hd using 1; ring)
        (fun x hx => sub_nonneg.mpr (ih4 x hx))
        (by rw [taylorCos_zero_at_zero _ (by omega), Real.cos_zero, sub_self]) hθ
      linarith
    have h2 : ∀ θ, 0 ≤ θ → Real.sin θ ≤ taylorSin (2 * (m + 1) + 1) θ := by
      intro θ hθ
      have := nonneg_of_deriv_nonneg
        (f := fun x => taylorSin (2 * (m + 1) + 1) x - Real.sin x)
        (f' := fun x => taylorCos (2 * (m + 1) + 1) x - Real.cos x)
        (fun x _ => (hasDerivAt_taylorSin _ x).sub (Real.hasDerivAt_sin x))
        (fun x hx => sub_nonneg.mpr (h1 x hx))
        (by simp [taylorSin_zero_at_zero]) hθ
      linarith
    have h3 : ∀ θ, 0 ≤ θ → taylorCos (2 * (m + 1) + 2) θ ≤ Real.cos θ := by
      intro θ hθ
      have hidx : 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 := by omega
      rw [hidx]
      have := nonneg_of_deriv_nonneg
        (f := fun x => Real.cos x - taylorCos ((2 * (m + 1) + 1) + 1) x)
        (f' := fun x => taylorSin (2 * (m + 1) + 1) x - Real.sin x)
        (fun x _ => by
          have hd := (Real.hasDerivAt_cos x).sub (hasDerivAt_taylorCos_succ (2 * (m + 1) + 1) x)
          convert hd using 1; ring)
        (fun x hx => sub_nonneg.mpr (h2 x hx))
        (by rw [Real.cos_zero, taylorCos_zero_at_zero _ (by omega), sub_self]) hθ
      linarith
    have h4 : ∀ θ, 0 ≤ θ → taylorSin (2 * (m + 1) + 2) θ ≤ Real.sin θ := by
      intro θ hθ
      have := nonneg_of_deriv_nonneg
        (f := fun x => Real.sin x - taylorSin (2 * (m + 1) + 2) x)
        (f' := fun x => Real.cos x - taylorCos (2 * (m + 1) + 2) x)
        (fun x _ => (Real.hasDerivAt_sin x).sub (hasDerivAt_taylorSin _ x))
        (fun x hx => sub_nonneg.mpr (h3 x hx))
        (by simp [taylorSin_zero_at_zero]) hθ
      linarith
    exact ⟨h1, h2, h3, h4⟩

/-- Elementary bound `1 - cos θ ≤ θ² / 2` for all `θ : ℝ`. -/
theorem one_sub_cos_le_sq_div_two (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have h := (taylor_trig_bounds 0).2.2.1 |θ| (abs_nonneg θ)
  rw [Real.cos_abs] at h
  simp only [taylorCos, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  norm_num [sq_abs] at h
  linarith

/-- Elementary lower bound `θ² / 2 - θ⁴ / 24 ≤ 1 - cos θ` for all `θ : ℝ`. -/
theorem sq_div_two_sub_pow4_div_24_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 ≤ 1 - Real.cos θ := by
  have h := (taylor_trig_bounds 1).1 |θ| (abs_nonneg θ)
  rw [Real.cos_abs] at h
  simp only [taylorCos, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  have hsq : |θ| ^ 2 = θ ^ 2 := sq_abs θ
  have h4 : |θ| ^ 4 = θ ^ 4 := by
    calc |θ| ^ 4 = (|θ| ^ 2) ^ 2 := by ring
      _ = (θ ^ 2) ^ 2 := by rw [hsq]
      _ = θ ^ 4 := by ring
  norm_num [hsq, h4] at h
  linarith

/-- Order-10 lower bound `taylorCos 6 θ ≤ cos θ` for `θ ≥ 0`. -/
theorem taylorCos6_le_cos {θ : ℝ} (hθ : 0 ≤ θ) :
    1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 ≤ Real.cos θ := by
  have h := (taylor_trig_bounds 2).2.2.1 θ hθ
  simp only [taylorCos, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  norm_num at h
  linarith

/-- Order-18 lower bound `taylorCos 10 θ ≤ cos θ` for `θ ≥ 0`. -/
theorem taylorCos10_le_cos {θ : ℝ} (hθ : 0 ≤ θ) :
    1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 +
      θ ^ 12 / 479001600 - θ ^ 14 / 87178291200 + θ ^ 16 / 20922789888000 -
      θ ^ 18 / 6402373705728000 ≤ Real.cos θ := by
  have h := (taylor_trig_bounds 4).2.2.1 θ hθ
  simp only [taylorCos, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  norm_num at h
  linarith

/-! ### 2. Jordan's Inequality and Strict Sinc Decay -/

/-- Jordan's inequality for `He(u²) = sin u / u` on `(0, π/2]`. -/
theorem two_div_pi_le_He_sq {u : ℝ} (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    2 / Real.pi ≤ He (u ^ 2) := by
  rw [He_sq hu0, le_div_iff₀ hu0]
  have h := Real.mul_le_sin hu0.le hu
  linarith

/-- Squared Jordan's inequality for `H(u²) = (sin u / u)²` on `(0, π/2]`. -/
theorem four_div_pi_sq_le_H_sq {u : ℝ} (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    4 / Real.pi ^ 2 ≤ H (u ^ 2) := by
  rw [H_sq hu0]
  have hj := two_div_pi_le_He_sq hu0 hu
  rw [He_sq hu0] at hj
  have hpos : 0 ≤ 2 / Real.pi := by positivity
  have hsq : (2 / Real.pi) ^ 2 ≤ (Real.sin u / u) ^ 2 := by nlinarith
  linarith [show (2 / Real.pi) ^ 2 = 4 / Real.pi ^ 2 by ring]

/-- Strict inequality `x * cos x < sin x` on `(0, π/2]`. -/
theorem mul_cos_lt_sin {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 2) :
    x * Real.cos x < Real.sin x := by
  have hstrict : StrictMonoOn (fun t : ℝ => Real.sin t - t * Real.cos t) (Set.Icc 0 (Real.pi / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 (Real.pi / 2)) ?_ ?_
    · exact (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      have hd : HasDerivAt (fun s : ℝ => Real.sin s - s * Real.cos s) (t * Real.sin t) t := by
        have h1 := (Real.hasDerivAt_sin t).fun_sub
          ((hasDerivAt_id' t).fun_mul (Real.hasDerivAt_cos t))
        refine h1.congr_deriv ?_
        ring
      rw [hd.deriv]
      exact mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
  have h0 := hstrict ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hx0.le, hx⟩ hx0
  simp at h0
  linarith

/-- Strict anti-monotonicity of `sin x / x` on `(0, π/2]`. -/
theorem strictAntiOn_sin_div_Ioc :
    StrictAntiOn (fun x : ℝ => Real.sin x / x) (Set.Ioc 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have hanti : StrictAntiOn (fun x : ℝ => Real.sin x / x) (Set.Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) ?_ ?_
    · exact Real.continuous_sin.continuousOn.div continuousOn_id fun x hx => by
        linarith [ha.1, hx.1]
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [ha.1, hx.1]
      have hxle : x ≤ Real.pi / 2 := by linarith [hb.2, hx.2]
      have hd : HasDerivAt (fun s : ℝ => Real.sin s / s)
          ((x * Real.cos x - Real.sin x) / x ^ 2) x := by
        have h1 := (Real.hasDerivAt_sin x).fun_div (hasDerivAt_id' x) hx0.ne'
        refine h1.congr_deriv ?_
        ring
      rw [hd.deriv]
      exact div_neg_of_neg_of_pos (sub_neg.mpr (mul_cos_lt_sin hx0 hxle)) (sq_pos_of_pos hx0)
  exact hanti (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab

/-- For EVERY real `q > 1` and `u ∈ (0, π/2)`, `|sin(q u)| < q sin u`. -/
theorem abs_sin_mul_lt_mul_sin {q u : ℝ} (hq : 1 < q) (hu0 : 0 < u) (hu : u < Real.pi / 2) :
    |Real.sin (q * u)| < q * Real.sin u := by
  by_cases hqu : q * u ≤ Real.pi / 2
  · have hqu0 : 0 < q * u := mul_pos (by linarith) hu0
    have hsin_pos : 0 < Real.sin (q * u) :=
      Real.sin_pos_of_pos_of_lt_pi hqu0 (by linarith [Real.pi_pos])
    rw [abs_of_pos hsin_pos]
    have hlt := strictAntiOn_sin_div_Ioc ⟨hu0, hu.le⟩ ⟨hqu0, hqu⟩ (by nlinarith)
    have hmul := (div_lt_div_iff₀ hqu0 hu0).mp hlt
    nlinarith
  · push Not at hqu
    have hj := Real.mul_le_sin hu0.le hu.le
    have h1 : |Real.sin (q * u)| ≤ 1 := Real.abs_sin_le_one (q * u)
    have hpi : 0 < Real.pi := Real.pi_pos
    have h2 : 1 < (2 / Real.pi) * (q * u) := by
      have : 2 / Real.pi * (Real.pi / 2) = 1 := by field_simp [hpi.ne']
      nlinarith [div_pos (by norm_num : (0 : ℝ) < 2) hpi]
    have h3 : (2 / Real.pi) * (q * u) ≤ q * Real.sin u := by
      have : (2 / Real.pi) * (q * u) = q * (2 / Real.pi * u) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hj (by linarith)
    linarith

/-- Consequently, `sin²(x u) < x² sin² u` for EVERY real `x > 1` and `u ∈ (0, π/2)`. -/
theorem sin_sq_mul_lt_mul_sq_sin_sq {x u : ℝ} (hx : 1 < x) (hu0 : 0 < u) (hu : u < Real.pi / 2) :
    Real.sin (x * u) ^ 2 < x ^ 2 * Real.sin u ^ 2 := by
  have habs := abs_sin_mul_lt_mul_sin hx hu0 hu
  have hnonneg : 0 ≤ |Real.sin (x * u)| := abs_nonneg _
  have hsq : |Real.sin (x * u)| ^ 2 < (x * Real.sin u) ^ 2 := by nlinarith
  rw [sq_abs] at hsq
  linarith [show (x * Real.sin u) ^ 2 = x ^ 2 * Real.sin u ^ 2 by ring]

/-! ### 3. Derivatives of `He` and `H` on `(0, ∞)` -/

/-- First derivative of `He(w) = sin(√w)/√w` for `w > 0`. -/
noncomputable def HeDeriv (w : ℝ) : ℝ :=
  (Real.sqrt w * Real.cos (Real.sqrt w) - Real.sin (Real.sqrt w)) / (2 * w * Real.sqrt w)

/-- Second derivative of `He(w)` for `w > 0`. -/
noncomputable def HeDeriv2 (w : ℝ) : ℝ :=
  ((3 - w) * Real.sin (Real.sqrt w) - 3 * Real.sqrt w * Real.cos (Real.sqrt w)) /
    (4 * w ^ 2 * Real.sqrt w)

/-- First derivative of `H(w) = (1 - cos(2√w))/(2w)` for `w > 0`. -/
noncomputable def HDeriv (w : ℝ) : ℝ :=
  (Real.sqrt w * Real.sin (2 * Real.sqrt w) + Real.cos (2 * Real.sqrt w) - 1) / (2 * w ^ 2)

/-- Second derivative of `H(w)` for `w > 0`. -/
noncomputable def HDeriv2 (w : ℝ) : ℝ :=
  ((2 * w - 4) * Real.cos (2 * Real.sqrt w) - 5 * Real.sqrt w * Real.sin (2 * Real.sqrt w) + 4) /
    (4 * w ^ 3)

/-- Third derivative of `H(w)` for `w > 0`. -/
noncomputable def HDeriv3 (w : ℝ) : ℝ :=
  ((24 - 18 * w) * Real.cos (2 * Real.sqrt w) +
    (33 * Real.sqrt w - 4 * w * Real.sqrt w) * Real.sin (2 * Real.sqrt w) - 24) / (8 * w ^ 4)

theorem hasDerivAt_He {w : ℝ} (hw : 0 < w) : HasDerivAt He (HeDeriv w) w := by
  have hsq : HasDerivAt (fun v => Real.sqrt v) (1 / (2 * Real.sqrt w)) w := Real.hasDerivAt_sqrt hw.ne'
  have hsin : HasDerivAt (fun v => Real.sin (Real.sqrt v))
      (Real.cos (Real.sqrt w) * (1 / (2 * Real.sqrt w))) w := (Real.hasDerivAt_sin _).comp w hsq
  have hdiv := hsin.fun_div hsq (Real.sqrt_ne_zero'.mpr hw)
  have hloc : He =ᶠ[nhds w] fun v => Real.sin (Real.sqrt v) / Real.sqrt v := by
    filter_upwards [eventually_ne_nhds hw.ne'] with v hv
    simp [He, hv]
  refine (hdiv.congr_of_eventuallyEq hloc).congr_deriv ?_
  unfold HeDeriv
  have hsne : Real.sqrt w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  set s := Real.sqrt w
  have hs2 : w = s ^ 2 := (Real.sq_sqrt hw.le).symm
  clear_value s
  subst hs2
  field_simp [hsne]

theorem hasDerivAt_HeDeriv {w : ℝ} (hw : 0 < w) : HasDerivAt HeDeriv (HeDeriv2 w) w := by
  have hsq : HasDerivAt (fun v => Real.sqrt v) (1 / (2 * Real.sqrt w)) w := Real.hasDerivAt_sqrt hw.ne'
  have hcos : HasDerivAt (fun v => Real.cos (Real.sqrt v))
      (-Real.sin (Real.sqrt w) * (1 / (2 * Real.sqrt w))) w := (Real.hasDerivAt_cos _).comp w hsq
  have hsin : HasDerivAt (fun v => Real.sin (Real.sqrt v))
      (Real.cos (Real.sqrt w) * (1 / (2 * Real.sqrt w))) w := (Real.hasDerivAt_sin _).comp w hsq
  have hnum := (hsq.fun_mul hcos).fun_sub hsin
  have hden := ((hasDerivAt_id' w).const_mul (2 : ℝ)).fun_mul hsq
  have hsne : Real.sqrt w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  have hden_ne : 2 * w * Real.sqrt w ≠ 0 := by positivity
  have hdiv := hnum.fun_div hden hden_ne
  refine hdiv.congr_deriv ?_
  unfold HeDeriv2
  set s := Real.sqrt w
  have hs2 : w = s ^ 2 := (Real.sq_sqrt hw.le).symm
  clear_value s
  subst hs2
  field_simp [hsne]
  ring

theorem hasDerivAt_H {w : ℝ} (hw : 0 < w) : HasDerivAt H (HDeriv w) w := by
  have hsq : HasDerivAt (fun v => Real.sqrt v) (1 / (2 * Real.sqrt w)) w := Real.hasDerivAt_sqrt hw.ne'
  have h2sq : HasDerivAt (fun v => 2 * Real.sqrt v) (2 * (1 / (2 * Real.sqrt w))) w :=
    hsq.const_mul 2
  have hcos : HasDerivAt (fun v => Real.cos (2 * Real.sqrt v))
      (-Real.sin (2 * Real.sqrt w) * (2 * (1 / (2 * Real.sqrt w)))) w :=
    (Real.hasDerivAt_cos _).comp w h2sq
  have hnum := (hasDerivAt_const w (1 : ℝ)).fun_sub hcos
  have hden : HasDerivAt (fun v => 2 * v) (2 * 1) w := (hasDerivAt_id' w).const_mul 2
  have hdiv := hnum.fun_div hden (by positivity : 2 * w ≠ 0)
  have hloc : H =ᶠ[nhds w] fun v => (1 - Real.cos (2 * Real.sqrt v)) / (2 * v) := by
    filter_upwards [eventually_ne_nhds hw.ne'] with v hv
    simp [H, hv]
  refine (hdiv.congr_of_eventuallyEq hloc).congr_deriv ?_
  unfold HDeriv
  have hsne : Real.sqrt w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  set s := Real.sqrt w
  have hs2 : w = s ^ 2 := (Real.sq_sqrt hw.le).symm
  clear_value s
  subst hs2
  field_simp [hsne]
  ring

theorem hasDerivAt_HDeriv {w : ℝ} (hw : 0 < w) : HasDerivAt HDeriv (HDeriv2 w) w := by
  have hsq : HasDerivAt (fun v => Real.sqrt v) (1 / (2 * Real.sqrt w)) w := Real.hasDerivAt_sqrt hw.ne'
  have h2sq : HasDerivAt (fun v => 2 * Real.sqrt v) (2 * (1 / (2 * Real.sqrt w))) w :=
    hsq.const_mul 2
  have hsin : HasDerivAt (fun v => Real.sin (2 * Real.sqrt v))
      (Real.cos (2 * Real.sqrt w) * (2 * (1 / (2 * Real.sqrt w)))) w :=
    (Real.hasDerivAt_sin _).comp w h2sq
  have hcos : HasDerivAt (fun v => Real.cos (2 * Real.sqrt v))
      (-Real.sin (2 * Real.sqrt w) * (2 * (1 / (2 * Real.sqrt w)))) w :=
    (Real.hasDerivAt_cos _).comp w h2sq
  have hnum := ((hsq.fun_mul hsin).fun_add hcos).sub_const (1 : ℝ)
  have hden : HasDerivAt (fun v => 2 * v ^ 2) (2 * (2 * w ^ (2 - 1))) w :=
    (hasDerivAt_pow 2 w).const_mul 2
  have hdiv := hnum.fun_div hden (by positivity : 2 * w ^ 2 ≠ 0)
  refine hdiv.congr_deriv ?_
  unfold HDeriv2
  have hsne : Real.sqrt w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  set s := Real.sqrt w
  have hs2 : w = s ^ 2 := (Real.sq_sqrt hw.le).symm
  clear_value s
  subst hs2
  field_simp [hsne]
  ring

theorem hasDerivAt_HDeriv2 {w : ℝ} (hw : 0 < w) : HasDerivAt HDeriv2 (HDeriv3 w) w := by
  have hsq : HasDerivAt (fun v => Real.sqrt v) (1 / (2 * Real.sqrt w)) w := Real.hasDerivAt_sqrt hw.ne'
  have h2sq : HasDerivAt (fun v => 2 * Real.sqrt v) (2 * (1 / (2 * Real.sqrt w))) w :=
    hsq.const_mul 2
  have hsin : HasDerivAt (fun v => Real.sin (2 * Real.sqrt v))
      (Real.cos (2 * Real.sqrt w) * (2 * (1 / (2 * Real.sqrt w)))) w :=
    (Real.hasDerivAt_sin _).comp w h2sq
  have hcos : HasDerivAt (fun v => Real.cos (2 * Real.sqrt v))
      (-Real.sin (2 * Real.sqrt w) * (2 * (1 / (2 * Real.sqrt w)))) w :=
    (Real.hasDerivAt_cos _).comp w h2sq
  have h1 : HasDerivAt (fun v => 2 * v - 4) (2 * 1) w :=
    ((hasDerivAt_id' w).const_mul 2).sub_const 4
  have h2 : HasDerivAt (fun v => 5 * Real.sqrt v) (5 * (1 / (2 * Real.sqrt w))) w :=
    hsq.const_mul 5
  have hnum := ((h1.fun_mul hcos).fun_sub (h2.fun_mul hsin)).add_const (4 : ℝ)
  have hden : HasDerivAt (fun v => 4 * v ^ 3) (4 * (3 * w ^ 2)) w := by
    simpa using (hasDerivAt_pow 3 w).const_mul 4
  have hdiv := hnum.fun_div hden (by positivity : 4 * w ^ 3 ≠ 0)
  refine hdiv.congr_deriv ?_
  unfold HDeriv3
  have hsne : Real.sqrt w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
  set s := Real.sqrt w
  have hs2 : w = s ^ 2 := (Real.sq_sqrt hw.le).symm
  clear_value s
  subst hs2
  field_simp [hsne]
  ring

/-! ### 4. Positive-Kernel Cosine-Transform Identities & Single-Interval Bernstein Certificates -/

/-- Exact positive cosine-transform identity for `He''(x²)` (`6 × 6`). -/
theorem HeDeriv2_sq_eq_integral {x : ℝ} (hx : 0 < x) :
    HeDeriv2 (x ^ 2) = (1 / 32 : ℝ) * ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ 2 * Real.cos (x * s) := by
  let A : ℝ → ℝ := fun s =>
    ((1 - 2 * s ^ 2 + s ^ 4) / x - (-4 + 12 * s ^ 2) / x ^ 3 + 24 / x ^ 5)
  let B : ℝ → ℝ := fun s =>
    ((-4 * s + 4 * s ^ 3) / x ^ 2 - (24 * s) / x ^ 4)
  let F : ℝ → ℝ := fun s => A s * Real.sin (x * s) + B s * Real.cos (x * s)
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F ((1 - s ^ 2) ^ 2 * Real.cos (x * s)) s := by
    intro s _
    have hA : HasDerivAt A (((-4 * s + 4 * s ^ 3) / x) - (24 * s) / x ^ 3) s := by
      have ha1 : HasDerivAt (fun t : ℝ => (1 - 2 * t ^ 2 + t ^ 4) / x)
          ((0 - 2 * (2 * s ^ 1) + 4 * s ^ 3) / x) s := by
        exact ((((hasDerivAt_const s (1 : ℝ)).fun_sub ((hasDerivAt_pow 2 s).const_mul 2)).fun_add
          (hasDerivAt_pow 4 s)).div_const x)
      have ha2 : HasDerivAt (fun t : ℝ => (-4 + 12 * t ^ 2) / x ^ 3)
          ((0 + 12 * (2 * s ^ 1)) / x ^ 3) s := by
        exact (((hasDerivAt_const s (-4 : ℝ)).fun_add ((hasDerivAt_pow 2 s).const_mul 12)).div_const (x ^ 3))
      have ha3 : HasDerivAt (fun _ : ℝ => (24 : ℝ) / x ^ 5) 0 s := hasDerivAt_const s _
      refine ((ha1.fun_sub ha2).fun_add ha3).congr_deriv ?_
      ring
    have hB : HasDerivAt B (((-4 + 12 * s ^ 2) / x ^ 2) - 24 / x ^ 4) s := by
      have hb1 : HasDerivAt (fun t : ℝ => (-4 * t + 4 * t ^ 3) / x ^ 2)
          ((-4 * 1 + 4 * (3 * s ^ 2)) / x ^ 2) s := by
        exact ((((hasDerivAt_id' s).const_mul (-4 : ℝ)).fun_add
          ((hasDerivAt_pow 3 s).const_mul 4)).div_const (x ^ 2))
      have hb2 : HasDerivAt (fun t : ℝ => (24 * t) / x ^ 4) ((24 * 1) / x ^ 4) s := by
        exact (((hasDerivAt_id' s).const_mul 24).div_const (x ^ 4))
      refine (hb1.fun_sub hb2).congr_deriv ?_
      ring
    have hxs : HasDerivAt (fun t : ℝ => x * t) (x * 1) s := (hasDerivAt_id' s).const_mul x
    have hsin := (Real.hasDerivAt_sin (x * s)).comp s hxs
    have hcos := (Real.hasDerivAt_cos (x * s)).comp s hxs
    have hd := (hA.fun_mul hsin).fun_add (hB.fun_mul hcos)
    refine hd.congr_deriv ?_
    simp only [A, B, Function.comp_apply]
    field_simp [hx.ne']
    ring
  have hint : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ 2 * Real.cos (x * s))
      MeasureTheory.volume 0 1 := by
    exact (((continuous_const.sub (continuous_pow 2)).pow 2).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F, A, B, HeDeriv2, Real.sqrt_sq hx.le, mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [hx.ne']
  ring

/-- Positive kernel `K₂(s) = (1 - s)³ (3 + 9s + 8s²) / 60 ≥ 0` on `[0, 1]` for `H''(x²)`. -/
noncomputable def K2 (s : ℝ) : ℝ :=
  1 / 20 - 1 / 6 * s ^ 2 + 1 / 4 * s ^ 4 - 2 / 15 * s ^ 5

theorem K2_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ K2 s := by
  have heq : K2 s = (1 - s) ^ 3 * (3 + 9 * s + 8 * s ^ 2) / 60 := by unfold K2; ring
  rw [heq]
  have : 0 ≤ 1 - s := by linarith
  positivity

/-- Exact positive cosine-transform identity for `H''(x²)` (`7 × 7`). -/
theorem HDeriv2_sq_eq_integral {x : ℝ} (hx : 0 < x) :
    HDeriv2 (x ^ 2) = 4 * ∫ s in (0 : ℝ)..1, K2 s * Real.cos (2 * x * s) := by
  let a : ℝ := 2 * x
  have ha : a ≠ 0 := by positivity
  let A : ℝ → ℝ := fun s =>
    (1 / 20 - 1 / 6 * s ^ 2 + 1 / 4 * s ^ 4 - 2 / 15 * s ^ 5) / a -
    (-1 / 3 + 3 * s ^ 2 - 8 / 3 * s ^ 3) / a ^ 3 +
    (6 - 16 * s) / a ^ 5
  let B : ℝ → ℝ := fun s =>
    (-1 / 3 * s + s ^ 3 - 2 / 3 * s ^ 4) / a ^ 2 -
    (6 * s - 8 * s ^ 2) / a ^ 4 +
    (-16) / a ^ 6
  let F : ℝ → ℝ := fun s => A s * Real.sin (a * s) + B s * Real.cos (a * s)
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (K2 s * Real.cos (a * s)) s := by
    intro s _
    have hA : HasDerivAt A
        ((-1 / 3 * s + s ^ 3 - 2 / 3 * s ^ 4) / a -
         (6 * s - 8 * s ^ 2) / a ^ 3 + (-16) / a ^ 5) s := by
      have ha1 := ((((hasDerivAt_const s (1 / 20 : ℝ)).fun_sub ((hasDerivAt_pow 2 s).const_mul (1 / 6))).fun_add
        ((hasDerivAt_pow 4 s).const_mul (1 / 4))).fun_sub ((hasDerivAt_pow 5 s).const_mul (2 / 15))).div_const a
      have ha2 := (((hasDerivAt_const s (-1 / 3 : ℝ)).fun_add ((hasDerivAt_pow 2 s).const_mul 3)).fun_sub
        ((hasDerivAt_pow 3 s).const_mul (8 / 3))).div_const (a ^ 3)
      have ha3 := ((hasDerivAt_const s (6 : ℝ)).fun_sub ((hasDerivAt_id' s).const_mul 16)).div_const (a ^ 5)
      refine ((ha1.fun_sub ha2).fun_add ha3).congr_deriv ?_
      ring
    have hB : HasDerivAt B
        ((-1 / 3 + 3 * s ^ 2 - 8 / 3 * s ^ 3) / a ^ 2 -
         (6 - 16 * s) / a ^ 4) s := by
      have hb1 := ((((hasDerivAt_id' s).const_mul (-1 / 3 : ℝ)).fun_add (hasDerivAt_pow 3 s)).fun_sub
        ((hasDerivAt_pow 4 s).const_mul (2 / 3))).div_const (a ^ 2)
      have hb2 := (((hasDerivAt_id' s).const_mul 6).fun_sub ((hasDerivAt_pow 2 s).const_mul 8)).div_const (a ^ 4)
      have hb3 : HasDerivAt (fun _ : ℝ => (-16 : ℝ) / a ^ 6) 0 s := hasDerivAt_const s _
      refine ((hb1.fun_sub hb2).fun_add hb3).congr_deriv ?_
      ring
    have has_d : HasDerivAt (fun t : ℝ => a * t) (a * 1) s := (hasDerivAt_id' s).const_mul a
    have hsin := (Real.hasDerivAt_sin (a * s)).comp s has_d
    have hcos := (Real.hasDerivAt_cos (a * s)).comp s has_d
    have hd := (hA.fun_mul hsin).fun_add (hB.fun_mul hcos)
    refine hd.congr_deriv ?_
    simp only [A, B, K2, Function.comp_apply]
    field_simp [ha]
    ring
  have hint : IntervalIntegrable (fun s : ℝ => K2 s * Real.cos (a * s))
      MeasureTheory.volume 0 1 := by
    have hcont : Continuous K2 := by unfold K2; fun_prop
    exact (hcont.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  change HDeriv2 (x ^ 2) = 4 * ∫ s in (0 : ℝ)..1, K2 s * Real.cos (a * s)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F, A, B, a, HDeriv2, Real.sqrt_sq hx.le, mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [hx.ne']
  ring

/-- Positive kernel `K₃(s) = (1 - s)⁴ (5 + 20s + 29s² + 16s³) / 840 ≥ 0` on `[0, 1]` for `-H'''(x²)`. -/
noncomputable def K3 (s : ℝ) : ℝ :=
  1 / 168 - 1 / 40 * s ^ 2 + 1 / 24 * s ^ 4 - 1 / 24 * s ^ 6 + 2 / 105 * s ^ 7

theorem K3_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ K3 s := by
  have heq : K3 s = (1 - s) ^ 4 * (5 + 20 * s + 29 * s ^ 2 + 16 * s ^ 3) / 840 := by
    unfold K3; ring
  rw [heq]
  have : 0 ≤ 1 - s := by linarith
  positivity

/-- Exact positive cosine-transform identity for `-H'''(x²)` (`9 × 9`). -/
theorem neg_HDeriv3_sq_eq_integral {x : ℝ} (hx : 0 < x) :
    -HDeriv3 (x ^ 2) = 8 * ∫ s in (0 : ℝ)..1, K3 s * Real.cos (2 * x * s) := by
  let a : ℝ := 2 * x
  have ha : a ≠ 0 := by positivity
  let A : ℝ → ℝ := fun s =>
    (1 / 168 - 1 / 40 * s ^ 2 + 1 / 24 * s ^ 4 - 1 / 24 * s ^ 6 + 2 / 105 * s ^ 7) / a -
    (-1 / 20 + 1 / 2 * s ^ 2 - 5 / 4 * s ^ 4 + 4 / 5 * s ^ 5) / a ^ 3 +
    (1 - 15 * s ^ 2 + 16 * s ^ 3) / a ^ 5 -
    (-30 + 96 * s) / a ^ 7
  let B : ℝ → ℝ := fun s =>
    (-1 / 20 * s + 1 / 6 * s ^ 3 - 1 / 4 * s ^ 5 + 2 / 15 * s ^ 6) / a ^ 2 -
    (s - 5 * s ^ 3 + 4 * s ^ 4) / a ^ 4 +
    (-30 * s + 48 * s ^ 2) / a ^ 6 -
    96 / a ^ 8
  let F : ℝ → ℝ := fun s => A s * Real.sin (a * s) + B s * Real.cos (a * s)
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (K3 s * Real.cos (a * s)) s := by
    intro s _
    have hA : HasDerivAt A
        ((-1 / 20 * s + 1 / 6 * s ^ 3 - 1 / 4 * s ^ 5 + 2 / 15 * s ^ 6) / a -
         (s - 5 * s ^ 3 + 4 * s ^ 4) / a ^ 3 +
         (-30 * s + 48 * s ^ 2) / a ^ 5 - 96 / a ^ 7) s := by
      have ha1 := (((((hasDerivAt_const s (1 / 168 : ℝ)).fun_sub ((hasDerivAt_pow 2 s).const_mul (1 / 40))).fun_add
        ((hasDerivAt_pow 4 s).const_mul (1 / 24))).fun_sub ((hasDerivAt_pow 6 s).const_mul (1 / 24))).fun_add
        ((hasDerivAt_pow 7 s).const_mul (2 / 105))).div_const a
      have ha2 := ((((hasDerivAt_const s (-1 / 20 : ℝ)).fun_add ((hasDerivAt_pow 2 s).const_mul (1 / 2))).fun_sub
        ((hasDerivAt_pow 4 s).const_mul (5 / 4))).fun_add ((hasDerivAt_pow 5 s).const_mul (4 / 5))).div_const (a ^ 3)
      have ha3 := (((hasDerivAt_const s (1 : ℝ)).fun_sub ((hasDerivAt_pow 2 s).const_mul 15)).fun_add
        ((hasDerivAt_pow 3 s).const_mul 16)).div_const (a ^ 5)
      have ha4 := ((hasDerivAt_const s (-30 : ℝ)).fun_add ((hasDerivAt_id' s).const_mul 96)).div_const (a ^ 7)
      refine (((ha1.fun_sub ha2).fun_add ha3).fun_sub ha4).congr_deriv ?_
      ring
    have hB : HasDerivAt B
        ((-1 / 20 + 1 / 2 * s ^ 2 - 5 / 4 * s ^ 4 + 4 / 5 * s ^ 5) / a ^ 2 -
         (1 - 15 * s ^ 2 + 16 * s ^ 3) / a ^ 4 +
         (-30 + 96 * s) / a ^ 6) s := by
      have hb1 := (((((hasDerivAt_id' s).const_mul (-1 / 20 : ℝ)).fun_add ((hasDerivAt_pow 3 s).const_mul (1 / 6))).fun_sub
        ((hasDerivAt_pow 5 s).const_mul (1 / 4))).fun_add ((hasDerivAt_pow 6 s).const_mul (2 / 15))).div_const (a ^ 2)
      have hb2 := (((hasDerivAt_id' s).fun_sub ((hasDerivAt_pow 3 s).const_mul 5)).fun_add
        ((hasDerivAt_pow 4 s).const_mul 4)).div_const (a ^ 4)
      have hb3 := (((hasDerivAt_id' s).const_mul (-30 : ℝ)).fun_add ((hasDerivAt_pow 2 s).const_mul 48)).div_const (a ^ 6)
      have hb4 : HasDerivAt (fun _ : ℝ => (96 : ℝ) / a ^ 8) 0 s := hasDerivAt_const s _
      refine (((hb1.fun_sub hb2).fun_add hb3).fun_sub hb4).congr_deriv ?_
      ring
    have has_d : HasDerivAt (fun t : ℝ => a * t) (a * 1) s := (hasDerivAt_id' s).const_mul a
    have hsin := (Real.hasDerivAt_sin (a * s)).comp s has_d
    have hcos := (Real.hasDerivAt_cos (a * s)).comp s has_d
    have hd := (hA.fun_mul hsin).fun_add (hB.fun_mul hcos)
    refine hd.congr_deriv ?_
    simp only [A, B, K3, Function.comp_apply]
    field_simp [ha]
    ring
  have hint : IntervalIntegrable (fun s : ℝ => K3 s * Real.cos (a * s))
      MeasureTheory.volume 0 1 := by
    have hcont : Continuous K3 := by unfold K3; fun_prop
    exact (hcont.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  change -HDeriv3 (x ^ 2) = 8 * ∫ s in (0 : ℝ)..1, K3 s * Real.cos (a * s)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp only [F, A, B, a, HDeriv3, Real.sqrt_sq hx.le, mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp [hx.ne']
  ring

private theorem integral_pow_zero_one (k : ℕ) :
    ∫ s in (0 : ℝ)..1, s ^ k = 1 / ((k : ℝ) + 1) := by
  rw [integral_pow]
  simp

/-- Single-interval Bernstein positivity certificate: `He''(x²) > 0` for all `0 < x ≤ 11/2`. -/
theorem HeDeriv2_pos {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 11 / 2) : 0 < HeDeriv2 (x ^ 2) := by
  rw [HeDeriv2_sq_eq_integral hx0]
  have hmono :
      ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ 2 *
        (1 - (x * s) ^ 2 / 2 + (x * s) ^ 4 / 24 - (x * s) ^ 6 / 720 +
          (x * s) ^ 8 / 40320 - (x * s) ^ 10 / 3628800) ≤
      ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ 2 * Real.cos (x * s) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s hs => ?_
    · exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact mul_le_mul_of_nonneg_left (taylorCos6_le_cos (mul_nonneg hx0.le hs.1)) (sq_nonneg _)
  have heval :
      (1 / 32 : ℝ) * ∫ s in (0 : ℝ)..1, (1 - s ^ 2) ^ 2 *
        (1 - (x * s) ^ 2 / 2 + (x * s) ^ 4 / 24 - (x * s) ^ 6 / 720 +
          (x * s) ^ 8 / 40320 - (x * s) ^ 10 / 3628800) =
      1 / 60 - 1 / 840 * (x ^ 2) + 1 / 30240 * (x ^ 2) ^ 2 - 1 / 1995840 * (x ^ 2) ^ 3 +
        1 / 207567360 * (x ^ 2) ^ 4 - 1 / 31135104000 * (x ^ 2) ^ 5 := by
    have hexp : ∀ s : ℝ,
        (1 - s ^ 2) ^ 2 *
          (1 - (x * s) ^ 2 / 2 + (x * s) ^ 4 / 24 - (x * s) ^ 6 / 720 +
            (x * s) ^ 8 / 40320 - (x * s) ^ 10 / 3628800) =
        (1 : ℝ) * s ^ 0 + (-2 - x ^ 2 / 2) * s ^ 2 + (1 + x ^ 2 + x ^ 4 / 24) * s ^ 4 +
        (-x ^ 2 / 2 - x ^ 4 / 12 - x ^ 6 / 720) * s ^ 6 +
        (x ^ 4 / 24 + x ^ 6 / 360 + x ^ 8 / 40320) * s ^ 8 +
        (-x ^ 6 / 720 - x ^ 8 / 20160 - x ^ 10 / 3628800) * s ^ 10 +
        (x ^ 8 / 40320 + x ^ 10 / 1814400) * s ^ 12 +
        (-x ^ 10 / 3628800) * s ^ 14 := fun s => by ring
    simp_rw [hexp]
    repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, integral_pow_zero_one]
    norm_num
    ring
  have hpos : 0 < 1 / 60 - 1 / 840 * (x ^ 2) + 1 / 30240 * (x ^ 2) ^ 2 -
      1 / 1995840 * (x ^ 2) ^ 3 + 1 / 207567360 * (x ^ 2) ^ 4 -
      1 / 31135104000 * (x ^ 2) ^ 5 := by
    set w := x ^ 2
    set W : ℝ := 121 / 4
    have hw0 : 0 < w := sq_pos_of_pos hx0
    have hwW : 0 ≤ W - w := by
      simp only [W, w]
      nlinarith
    have hbern : W ^ 5 * (1 / 60 - 1 / 840 * w + 1 / 30240 * w ^ 2 -
        1 / 1995840 * w ^ 3 + 1 / 207567360 * w ^ 4 - 1 / 31135104000 * w ^ 5) =
        (1 / 60) * (W - w) ^ 5 + (53 / 1120) * w * (W - w) ^ 4 +
        (731 / 13824) * w ^ 2 * (W - w) ^ 3 + (63881 / 2322432) * w ^ 3 * (W - w) ^ 2 +
        (3414443 / 536739840) * w ^ 4 * (W - w) +
        (771327709 / 2898395136000) * w ^ 5 := by
      simp only [W]; ring
    have hrhs : 0 < (1 / 60 : ℝ) * (W - w) ^ 5 + (53 / 1120) * w * (W - w) ^ 4 +
        (731 / 13824) * w ^ 2 * (W - w) ^ 3 + (63881 / 2322432) * w ^ 3 * (W - w) ^ 2 +
        (3414443 / 536739840) * w ^ 4 * (W - w) +
        (771327709 / 2898395136000) * w ^ 5 := by positivity
    have hW5 : 0 < W ^ 5 := by positivity
    nlinarith
  linarith

/-- Single-interval Bernstein positivity certificate: `H''(x²) > 0` for all `0 < x ≤ 33/10`. -/
theorem HDeriv2_pos {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 33 / 10) : 0 < HDeriv2 (x ^ 2) := by
  rw [HDeriv2_sq_eq_integral hx0]
  have hmono :
      ∫ s in (0 : ℝ)..1, K2 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800) ≤
      ∫ s in (0 : ℝ)..1, K2 s * Real.cos (2 * x * s) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s hs => ?_
    · unfold K2; exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · unfold K2; exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact mul_le_mul_of_nonneg_left
        (taylorCos6_le_cos (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * x) hs.1)) (K2_nonneg hs.1 hs.2)
  have heval :
      4 * ∫ s in (0 : ℝ)..1, K2 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800) =
      4 / 45 - 2 / 105 * (x ^ 2) + 8 / 4725 * (x ^ 2) ^ 2 - 8 / 93555 * (x ^ 2) ^ 3 +
        8 / 2837835 * (x ^ 2) ^ 4 - 2 / 30405375 * (x ^ 2) ^ 5 := by
    have hexp : ∀ s : ℝ,
        K2 s * (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800) =
        (1 / 20 : ℝ) * s ^ 0 + (-1 / 6 - 1 / 10 * x ^ 2) * s ^ 2 +
        (1 / 4 + 1 / 3 * x ^ 2 + 1 / 30 * x ^ 4) * s ^ 4 + (-2 / 15 : ℝ) * s ^ 5 +
        (-1 / 2 * x ^ 2 - 1 / 9 * x ^ 4 - 2 / 450 * x ^ 6) * s ^ 6 +
        (4 / 15 * x ^ 2) * s ^ 7 +
        (1 / 6 * x ^ 4 + 2 / 135 * x ^ 6 + 4 / 12600 * x ^ 8) * s ^ 8 +
        (-4 / 45 * x ^ 4) * s ^ 9 +
        (-1 / 45 * x ^ 6 - 2 / 1890 * x ^ 8 - 1 / 70875 * x ^ 10) * s ^ 10 +
        (8 / 675 * x ^ 6) * s ^ 11 +
        (1 / 630 * x ^ 8 + 2 / 42525 * x ^ 10) * s ^ 12 +
        (-16 / 18900 * x ^ 8) * s ^ 13 +
        (-1 / 14175 * x ^ 10) * s ^ 14 +
        (16 / 425250 * x ^ 10) * s ^ 15 := by
      intro s; unfold K2; ring
    simp_rw [hexp]
    repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, integral_pow_zero_one]
    norm_num
    ring
  have hpos : 0 < 4 / 45 - 2 / 105 * (x ^ 2) + 8 / 4725 * (x ^ 2) ^ 2 -
      8 / 93555 * (x ^ 2) ^ 3 + 8 / 2837835 * (x ^ 2) ^ 4 - 2 / 30405375 * (x ^ 2) ^ 5 := by
    set w := x ^ 2
    set W : ℝ := 1089 / 100
    have hw0 : 0 < w := sq_pos_of_pos hx0
    have hwW : 0 ≤ W - w := by
      simp only [W, w]
      nlinarith
    have hbern : W ^ 5 * (4 / 45 - 2 / 105 * w + 8 / 4725 * w ^ 2 -
        8 / 93555 * w ^ 3 + 8 / 2837835 * w ^ 4 - 2 / 30405375 * w ^ 5) =
        (4 / 45) * (W - w) ^ 5 + (3733 / 15750) * w * (W - w) ^ 4 +
        (511807 / 1968750) * w ^ 2 * (W - w) ^ 3 + (5365043 / 39375000) * w ^ 3 * (W - w) ^ 2 +
        (12856308259 / 358312500000) * w ^ 4 * (W - w) +
        (4977588388481 / 3583125000000000) * w ^ 5 := by
      simp only [W]; ring
    have hrhs : 0 < (4 / 45 : ℝ) * (W - w) ^ 5 + (3733 / 15750) * w * (W - w) ^ 4 +
        (511807 / 1968750) * w ^ 2 * (W - w) ^ 3 + (5365043 / 39375000) * w ^ 3 * (W - w) ^ 2 +
        (12856308259 / 358312500000) * w ^ 4 * (W - w) +
        (4977588388481 / 3583125000000000) * w ^ 5 := by positivity
    have hW5 : 0 < W ^ 5 := by positivity
    nlinarith
  linarith

/-- Moment identity `∫_0^1 K₃(s) s^(2j) ds` for evaluating the degree-9 Bernstein lower bound. -/
private theorem integral_K3_mul_pow (m : ℕ) :
    ∫ s in (0 : ℝ)..1, K3 s * s ^ m =
      1 / 168 * (1 / ((m : ℝ) + 1)) - 1 / 40 * (1 / ((m : ℝ) + 3)) +
      1 / 24 * (1 / ((m : ℝ) + 5)) - 1 / 24 * (1 / ((m : ℝ) + 7)) +
      2 / 105 * (1 / ((m : ℝ) + 8)) := by
  have hexp : ∀ s : ℝ, K3 s * s ^ m =
      (1 / 168 : ℝ) * s ^ m + (-1 / 40 : ℝ) * s ^ (m + 2) +
      (1 / 24 : ℝ) * s ^ (m + 4) + (-1 / 24 : ℝ) * s ^ (m + 6) +
      (2 / 105 : ℝ) * s ^ (m + 7) := by
    intro s; unfold K3; ring
  simp_rw [hexp]
  repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  simp_rw [intervalIntegral.integral_const_mul, integral_pow_zero_one]
  push_cast
  ring

/-- Single-interval Bernstein certificate: `H'''(x²) < 0` for all `0 < x ≤ 83/20` (`4.15`). -/
theorem HDeriv3_neg {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 83 / 20) : HDeriv3 (x ^ 2) < 0 := by
  suffices h : 0 < -HDeriv3 (x ^ 2) by linarith
  rw [neg_HDeriv3_sq_eq_integral hx0]
  have hmono :
      ∫ s in (0 : ℝ)..1, K3 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800 +
          (2 * x * s) ^ 12 / 479001600 - (2 * x * s) ^ 14 / 87178291200 +
          (2 * x * s) ^ 16 / 20922789888000 - (2 * x * s) ^ 18 / 6402373705728000) ≤
      ∫ s in (0 : ℝ)..1, K3 s * Real.cos (2 * x * s) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s hs => ?_
    · unfold K3; exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · unfold K3; exact (by fun_prop : Continuous _).intervalIntegrable 0 1
    · exact mul_le_mul_of_nonneg_left
        (taylorCos10_le_cos (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * x) hs.1)) (K3_nonneg hs.1 hs.2)
  have heval :
      8 * ∫ s in (0 : ℝ)..1, K3 s *
        (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800 +
          (2 * x * s) ^ 12 / 479001600 - (2 * x * s) ^ 14 / 87178291200 +
          (2 * x * s) ^ 16 / 20922789888000 - (2 * x * s) ^ 18 / 6402373705728000) =
      2 / 105 - 16 / 4725 * (x ^ 2) + 8 / 31185 * (x ^ 2) ^ 2 -
        32 / 2837835 * (x ^ 2) ^ 3 + 2 / 6081075 * (x ^ 2) ^ 4 -
        32 / 4652022375 * (x ^ 2) ^ 5 + 16 / 147314041875 * (x ^ 2) ^ 6 -
        64 / 47641361142375 * (x ^ 2) ^ 7 + 4 / 298841265347625 * (x ^ 2) ^ 8 -
        32 / 291370233713934375 * (x ^ 2) ^ 9 := by
    have hsplit : ∀ s : ℝ,
        K3 s * (1 - (2 * x * s) ^ 2 / 2 + (2 * x * s) ^ 4 / 24 - (2 * x * s) ^ 6 / 720 +
          (2 * x * s) ^ 8 / 40320 - (2 * x * s) ^ 10 / 3628800 +
          (2 * x * s) ^ 12 / 479001600 - (2 * x * s) ^ 14 / 87178291200 +
          (2 * x * s) ^ 16 / 20922789888000 - (2 * x * s) ^ 18 / 6402373705728000) =
        (1 : ℝ) * (K3 s * s ^ 0) + (-(2 * x) ^ 2 / 2) * (K3 s * s ^ 2) +
        ((2 * x) ^ 4 / 24) * (K3 s * s ^ 4) + (-(2 * x) ^ 6 / 720) * (K3 s * s ^ 6) +
        ((2 * x) ^ 8 / 40320) * (K3 s * s ^ 8) + (-(2 * x) ^ 10 / 3628800) * (K3 s * s ^ 10) +
        ((2 * x) ^ 12 / 479001600) * (K3 s * s ^ 12) +
        (-(2 * x) ^ 14 / 87178291200) * (K3 s * s ^ 14) +
        ((2 * x) ^ 16 / 20922789888000) * (K3 s * s ^ 16) +
        (-(2 * x) ^ 18 / 6402373705728000) * (K3 s * s ^ 18) := fun s => by ring
    simp_rw [hsplit]
    have hK3c : Continuous K3 := by unfold K3; fun_prop
    repeat rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp_rw [intervalIntegral.integral_const_mul, integral_K3_mul_pow]
    norm_num
    ring
  have hpos : 0 < 2 / 105 - 16 / 4725 * (x ^ 2) + 8 / 31185 * (x ^ 2) ^ 2 -
      32 / 2837835 * (x ^ 2) ^ 3 + 2 / 6081075 * (x ^ 2) ^ 4 -
      32 / 4652022375 * (x ^ 2) ^ 5 + 16 / 147314041875 * (x ^ 2) ^ 6 -
      64 / 47641361142375 * (x ^ 2) ^ 7 + 4 / 298841265347625 * (x ^ 2) ^ 8 -
      32 / 291370233713934375 * (x ^ 2) ^ 9 := by
    set w := x ^ 2
    set W : ℝ := 6889 / 400
    have hw0 : 0 < w := sq_pos_of_pos hx0
    have hwW : 0 ≤ W - w := by
      simp only [W, w]
      nlinarith
    have hbern : W ^ 9 * (2 / 105 - 16 / 4725 * w + 8 / 31185 * w ^ 2 -
        32 / 2837835 * w ^ 3 + 2 / 6081075 * w ^ 4 -
        32 / 4652022375 * w ^ 5 + 16 / 147314041875 * w ^ 6 -
        64 / 47641361142375 * w ^ 7 + 4 / 298841265347625 * w ^ 8 -
        32 / 291370233713934375 * w ^ 9) =
        (2 / 105) * (W - w) ^ 9 +
        (13361 / 118125) * w * (W - w) ^ 8 +
        (184146961 / 623700000) * w ^ 2 * (W - w) ^ 7 +
        (836383952777 / 1891890000000) * w ^ 3 * (W - w) ^ 6 +
        (20573069784548117 / 49533120000000000) * w ^ 4 * (W - w) ^ 5 +
        (81746855076292799851 / 325641566250000000000) * w ^ 5 * (W - w) ^ 4 +
        (75816229327372874018141381 / 791960289120000000000000000) * w ^ 6 * (W - w) ^ 3 +
        (26039967813928468601331901091 / 1219618845244800000000000000000) * w ^ 7 * (W - w) ^ 2 +
        (1225879774622498926032130370815691 / 538583682060103680000000000000000000) * w ^ 8 * (W - w) +
        (66536347679968549508017944175026829 / 1381892342127897600000000000000000000000) * w ^ 9 := by
      simp only [W]; ring
    have hrhs : 0 < (2 / 105 : ℝ) * (W - w) ^ 9 +
        (13361 / 118125) * w * (W - w) ^ 8 +
        (184146961 / 623700000) * w ^ 2 * (W - w) ^ 7 +
        (836383952777 / 1891890000000) * w ^ 3 * (W - w) ^ 6 +
        (20573069784548117 / 49533120000000000) * w ^ 4 * (W - w) ^ 5 +
        (81746855076292799851 / 325641566250000000000) * w ^ 5 * (W - w) ^ 4 +
        (75816229327372874018141381 / 791960289120000000000000000) * w ^ 6 * (W - w) ^ 3 +
        (26039967813928468601331901091 / 1219618845244800000000000000000) * w ^ 7 * (W - w) ^ 2 +
        (1225879774622498926032130370815691 / 538583682060103680000000000000000000) * w ^ 8 * (W - w) +
        (66536347679968549508017944175026829 / 1381892342127897600000000000000000000000) * w ^ 9 := by
      positivity
    have hW9 : 0 < W ^ 9 := by positivity
    nlinarith
  linarith

/-! ### 5. Global Strict Monotonicity of Divided-Difference Slopes (`6 × 6` and `7 × 7`) -/

/-- For every `u ∈ (0, π/2)` and every `w > u²`, `He(u²) - He(w) + (w - u²) He'(w) > 0`. -/
theorem He_slope_num_pos {u w : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2) (hw : u ^ 2 < w) :
    0 < He (u ^ 2) - He w + (w - u ^ 2) * HeDeriv w := by
  have hw0 : 0 < w := lt_trans (sq_pos_of_pos hu0) hw
  set x := Real.sqrt w
  have hx0 : 0 < x := Real.sqrt_pos.mpr hw0
  have hxw : x ^ 2 = w := Real.sq_sqrt hw0.le
  by_cases hx : x ≤ 11 / 2
  · let φ : ℝ → ℝ := fun v => He (u ^ 2) - He v + (v - u ^ 2) * HeDeriv v
    have hstrict : StrictMonoOn φ (Set.Icc (u ^ 2) w) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc (u ^ 2) w) ?_ ?_
      · intro v hv
        have hv0 : 0 < v := lt_of_lt_of_le (sq_pos_of_pos hu0) hv.1
        have hd : HasDerivAt φ ((v - u ^ 2) * HeDeriv2 v) v := by
          have h1 := ((hasDerivAt_const v (He (u ^ 2))).fun_sub (hasDerivAt_He hv0)).fun_add
            (((hasDerivAt_id' v).sub_const (u ^ 2)).fun_mul (hasDerivAt_HeDeriv hv0))
          refine h1.congr_deriv ?_
          ring
        exact hd.continuousAt.continuousWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        have hv0 : 0 < v := lt_trans (sq_pos_of_pos hu0) hv.1
        have hd : HasDerivAt φ ((v - u ^ 2) * HeDeriv2 v) v := by
          have h1 := ((hasDerivAt_const v (He (u ^ 2))).fun_sub (hasDerivAt_He hv0)).fun_add
            (((hasDerivAt_id' v).sub_const (u ^ 2)).fun_mul (hasDerivAt_HeDeriv hv0))
          refine h1.congr_deriv ?_
          ring
        rw [hd.deriv]
        have hsqrt_le : Real.sqrt v ≤ 11 / 2 :=
          le_trans (Real.sqrt_le_sqrt hv.2.le) hx
        have h2pos : 0 < HeDeriv2 v := by
          have := HeDeriv2_pos (Real.sqrt_pos.mpr hv0) hsqrt_le
          rwa [Real.sq_sqrt hv0.le] at this
        exact mul_pos (sub_pos.mpr hv.1) h2pos
    have h0 := hstrict (Set.left_mem_Icc.mpr hw.le) (Set.right_mem_Icc.mpr hw.le) hw
    simp only [φ, sub_self, zero_mul, add_zero] at h0
    exact h0
  · push Not at hx
    have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
    have hHe_lb : 63 / 100 < He (u ^ 2) := by
      have hj := two_div_pi_le_He_sq hu0 hu.le
      have hdiv : (63 / 100 : ℝ) < 2 / Real.pi := by
        rw [lt_div_iff₀ Real.pi_pos]
        linarith
      linarith
    have hdecomp : He w - (w - u ^ 2) * HeDeriv w =
        (3 * Real.sin x - x * Real.cos x) / (2 * x) +
        u ^ 2 * (x * Real.cos x - Real.sin x) / (2 * x ^ 3) := by
      rw [← hxw, He_sq hx0]
      unfold HeDeriv
      rw [Real.sqrt_sq hx0.le]
      field_simp [hx0.ne']
      ring
    have hcs1 : (3 * Real.sin x - x * Real.cos x) / (2 * x) ≤ 57 / 100 := by
      have hsq1 : ((3 * Real.sin x - x * Real.cos x) / (2 * x)) ^ 2 ≤ (57 / 100 : ℝ) ^ 2 := by
        have htrig : (3 * Real.sin x - x * Real.cos x) ^ 2 ≤ 9 + x ^ 2 := by
          have h := Real.sin_sq_add_cos_sq x
          nlinarith [sq_nonneg (3 * Real.cos x + x * Real.sin x)]
        have hnum : 9 + x ^ 2 ≤ (57 / 100 : ℝ) ^ 2 * (2 * x) ^ 2 := by
          have hx2 : (121 / 4 : ℝ) < x ^ 2 := by nlinarith
          nlinarith
        rw [div_pow]
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * x) ^ 2)).mpr (le_trans htrig hnum)
      nlinarith
    have hcs2 : (x * Real.cos x - Real.sin x) / (2 * x ^ 3) ≤ 2 / 100 := by
      have hsq2 : ((x * Real.cos x - Real.sin x) / (2 * x ^ 3)) ^ 2 ≤ (2 / 100 : ℝ) ^ 2 := by
        have htrig : (x * Real.cos x - Real.sin x) ^ 2 ≤ 1 + x ^ 2 := by
          have h := Real.sin_sq_add_cos_sq x
          nlinarith [sq_nonneg (x * Real.sin x + Real.cos x)]
        have hx2 : (121 / 4 : ℝ) < x ^ 2 := by nlinarith
        have hx4 : (121 / 4 : ℝ) ^ 2 < x ^ 4 := by nlinarith
        have hx6 : (121 / 4 : ℝ) ^ 3 < x ^ 6 := by nlinarith
        have hnum : 1 + x ^ 2 ≤ (2 / 100 : ℝ) ^ 2 * (2 * x ^ 3) ^ 2 := by
          have : (2 * x ^ 3) ^ 2 = 4 * x ^ 6 := by ring
          rw [this]
          have h1 : x ^ 2 ≤ x ^ 6 / (121 / 4 : ℝ) ^ 2 := by
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < (121 / 4 : ℝ) ^ 2)]
            nlinarith
          nlinarith
        rw [div_pow]
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * x ^ 3) ^ 2)).mpr (le_trans htrig hnum)
      nlinarith
    have hu2 : u ^ 2 ≤ 5 / 2 := by nlinarith [Real.pi_pos]
    have hterm2 : u ^ 2 * (x * Real.cos x - Real.sin x) / (2 * x ^ 3) ≤ 5 / 100 := by
      have : u ^ 2 * (x * Real.cos x - Real.sin x) / (2 * x ^ 3) =
          u ^ 2 * ((x * Real.cos x - Real.sin x) / (2 * x ^ 3)) := by ring
      rw [this]
      nlinarith [sq_nonneg u]
    linarith

/-- Global strict anti-monotonicity of `w ↦ (He(u²) - He(w)) / (w - u²)` on `(u², ∞)` (`6 × 6`). -/
theorem He_slope_strictAnti {u w1 w2 : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hw1 : u ^ 2 < w1) (hw12 : w1 < w2) :
    (He (u ^ 2) - He w2) / (w2 - u ^ 2) < (He (u ^ 2) - He w1) / (w1 - u ^ 2) := by
  let G : ℝ → ℝ := fun w => (He (u ^ 2) - He w) / (w - u ^ 2)
  have hanti : StrictAntiOn G (Set.Icc w1 w2) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc w1 w2) ?_ ?_
    · intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le (lt_trans (sq_pos_of_pos hu0) hw1) hw.1
      have hne : w - u ^ 2 ≠ 0 := by linarith [hw.1]
      have hd : HasDerivAt G
          (-(He (u ^ 2) - He w + (w - u ^ 2) * HeDeriv w) / (w - u ^ 2) ^ 2) w := by
        have h1 := ((hasDerivAt_const w (He (u ^ 2))).fun_sub (hasDerivAt_He hw0)).fun_div
          ((hasDerivAt_id' w).sub_const (u ^ 2)) hne
        refine h1.congr_deriv ?_
        ring
      exact hd.continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hwu : u ^ 2 < w := lt_trans hw1 hw.1
      have hw0 : 0 < w := lt_trans (sq_pos_of_pos hu0) hwu
      have hne : w - u ^ 2 ≠ 0 := (sub_pos.mpr hwu).ne'
      have hd : HasDerivAt G
          (-(He (u ^ 2) - He w + (w - u ^ 2) * HeDeriv w) / (w - u ^ 2) ^ 2) w := by
        have h1 := ((hasDerivAt_const w (He (u ^ 2))).fun_sub (hasDerivAt_He hw0)).fun_div
          ((hasDerivAt_id' w).sub_const (u ^ 2)) hne
        refine h1.congr_deriv ?_
        ring
      rw [hd.deriv]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (He_slope_num_pos hu0 hu hwu))
        (sq_pos_of_pos (sub_pos.mpr hwu))
  exact hanti (Set.left_mem_Icc.mpr hw12.le) (Set.right_mem_Icc.mpr hw12.le) hw12

/-- For every `u ∈ (0, π/2)` and every `w > u²`, `H(u²) - H(w) + (w - u²) H'(w) > 0` (`7 × 7`). -/
theorem H_slope_num_pos {u w : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2) (hw : u ^ 2 < w) :
    0 < H (u ^ 2) - H w + (w - u ^ 2) * HDeriv w := by
  have hw0 : 0 < w := lt_trans (sq_pos_of_pos hu0) hw
  set x := Real.sqrt w
  have hx0 : 0 < x := Real.sqrt_pos.mpr hw0
  have hxw : x ^ 2 = w := Real.sq_sqrt hw0.le
  by_cases hx : x ≤ 33 / 10
  · let φ : ℝ → ℝ := fun v => H (u ^ 2) - H v + (v - u ^ 2) * HDeriv v
    have hstrict : StrictMonoOn φ (Set.Icc (u ^ 2) w) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc (u ^ 2) w) ?_ ?_
      · intro v hv
        have hv0 : 0 < v := lt_of_lt_of_le (sq_pos_of_pos hu0) hv.1
        have hd : HasDerivAt φ ((v - u ^ 2) * HDeriv2 v) v := by
          have h1 := ((hasDerivAt_const v (H (u ^ 2))).fun_sub (hasDerivAt_H hv0)).fun_add
            (((hasDerivAt_id' v).sub_const (u ^ 2)).fun_mul (hasDerivAt_HDeriv hv0))
          refine h1.congr_deriv ?_
          ring
        exact hd.continuousAt.continuousWithinAt
      · intro v hv
        rw [interior_Icc] at hv
        have hv0 : 0 < v := lt_trans (sq_pos_of_pos hu0) hv.1
        have hd : HasDerivAt φ ((v - u ^ 2) * HDeriv2 v) v := by
          have h1 := ((hasDerivAt_const v (H (u ^ 2))).fun_sub (hasDerivAt_H hv0)).fun_add
            (((hasDerivAt_id' v).sub_const (u ^ 2)).fun_mul (hasDerivAt_HDeriv hv0))
          refine h1.congr_deriv ?_
          ring
        rw [hd.deriv]
        have hsqrt_le : Real.sqrt v ≤ 33 / 10 :=
          le_trans (Real.sqrt_le_sqrt hv.2.le) hx
        have h2pos : 0 < HDeriv2 v := by
          have := HDeriv2_pos (Real.sqrt_pos.mpr hv0) hsqrt_le
          rwa [Real.sq_sqrt hv0.le] at this
        exact mul_pos (sub_pos.mpr hv.1) h2pos
    have h0 := hstrict (Set.left_mem_Icc.mpr hw.le) (Set.right_mem_Icc.mpr hw.le) hw
    simp only [φ, sub_self, zero_mul, add_zero] at h0
    exact h0
  · push Not at hx
    have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
    have hH_lb : 4 / 10 < H (u ^ 2) := by
      have hj := four_div_pi_sq_le_H_sq hu0 hu.le
      have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
      have hdiv : (4 / 10 : ℝ) < 4 / Real.pi ^ 2 := by
        rw [div_lt_div_iff₀ (by norm_num) (sq_pos_of_pos Real.pi_pos)]
        linarith
      linarith
    have hdecomp : H w - (w - u ^ 2) * HDeriv w =
        (2 - 2 * Real.cos (2 * x) - x * Real.sin (2 * x)) / (2 * x ^ 2) +
        u ^ 2 * (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) / (2 * x ^ 4) := by
      have hH : H w = (1 - Real.cos (2 * x)) / (2 * x ^ 2) := by
        rw [← hxw]; simp [H, (sq_pos_of_pos hx0).ne', Real.sqrt_sq hx0.le]
      rw [hH]
      unfold HDeriv
      rw [← hxw, Real.sqrt_sq hx0.le]
      field_simp [hx0.ne']
      ring
    have hcos_lb : -1 ≤ Real.cos (2 * x) := Real.neg_one_le_cos (2 * x)
    have hcos_ub : Real.cos (2 * x) ≤ 1 := Real.cos_le_one (2 * x)
    have hsin_lb : -1 ≤ Real.sin (2 * x) := Real.neg_one_le_sin (2 * x)
    have hsin_ub : Real.sin (2 * x) ≤ 1 := Real.sin_le_one (2 * x)
    have ht1 : (2 - 2 * Real.cos (2 * x) - x * Real.sin (2 * x)) / (2 * x ^ 2) ≤ 34 / 100 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * x ^ 2)]
      nlinarith
    have hu2 : u ^ 2 ≤ 5 / 2 := by nlinarith [Real.pi_pos]
    have ht2 : u ^ 2 * (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) / (2 * x ^ 4) ≤ 4 / 100 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * x ^ 4)]
      have hnum : x * Real.sin (2 * x) + Real.cos (2 * x) - 1 ≤ x := by nlinarith
      have hmul : u ^ 2 * (x * Real.sin (2 * x) + Real.cos (2 * x) - 1) ≤ (5 / 2) * x := by
        by_cases hsign : 0 ≤ x * Real.sin (2 * x) + Real.cos (2 * x) - 1
        · nlinarith
        · nlinarith [sq_nonneg u]
      have hx3 : (33 / 10 : ℝ) ^ 3 < x ^ 3 := by nlinarith
      nlinarith
    linarith

/-- Global strict anti-monotonicity of `w ↦ (H(u²) - H(w)) / (w - u²)` on `(u², ∞)` (`7 × 7`). -/
theorem H_slope_strictAnti {u w1 w2 : ℝ} (hu0 : 0 < u) (hu : u < Real.pi / 2)
    (hw1 : u ^ 2 < w1) (hw12 : w1 < w2) :
    (H (u ^ 2) - H w2) / (w2 - u ^ 2) < (H (u ^ 2) - H w1) / (w1 - u ^ 2) := by
  let G : ℝ → ℝ := fun w => (H (u ^ 2) - H w) / (w - u ^ 2)
  have hanti : StrictAntiOn G (Set.Icc w1 w2) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc w1 w2) ?_ ?_
    · intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le (lt_trans (sq_pos_of_pos hu0) hw1) hw.1
      have hne : w - u ^ 2 ≠ 0 := by linarith [hw.1]
      have hd : HasDerivAt G
          (-(H (u ^ 2) - H w + (w - u ^ 2) * HDeriv w) / (w - u ^ 2) ^ 2) w := by
        have h1 := ((hasDerivAt_const w (H (u ^ 2))).fun_sub (hasDerivAt_H hw0)).fun_div
          ((hasDerivAt_id' w).sub_const (u ^ 2)) hne
        refine h1.congr_deriv ?_
        ring
      exact hd.continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Icc] at hw
      have hwu : u ^ 2 < w := lt_trans hw1 hw.1
      have hw0 : 0 < w := lt_trans (sq_pos_of_pos hu0) hwu
      have hne : w - u ^ 2 ≠ 0 := (sub_pos.mpr hwu).ne'
      have hd : HasDerivAt G
          (-(H (u ^ 2) - H w + (w - u ^ 2) * HDeriv w) / (w - u ^ 2) ^ 2) w := by
        have h1 := ((hasDerivAt_const w (H (u ^ 2))).fun_sub (hasDerivAt_H hw0)).fun_div
          ((hasDerivAt_id' w).sub_const (u ^ 2)) hne
        refine h1.congr_deriv ?_
        ring
      rw [hd.deriv]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (H_slope_num_pos hu0 hu hwu))
        (sq_pos_of_pos (sub_pos.mpr hwu))
  exact hanti (Set.left_mem_Icc.mpr hw12.le) (Set.right_mem_Icc.mpr hw12.le) hw12

end SpectralEclipse
