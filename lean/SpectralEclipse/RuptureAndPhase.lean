/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Conjecture41
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Sharp Rupture Dimensions (`8 × 8` and `11 × 11` at `M* = 12`) and the Universal `3R + 2` Phase Transition

Proves Theorems 5, 7, and 8 of the linked Early State Exclusion (ESE) chain:
  - **Theorem 5 (`even_rupture_8x8`)**: For EVERY integer `m ≥ 1`, the `8 × 8` symmetric PST chain
    `{±1/2, ±(4m+3)/2, ±(4m+5)/2, ±(4m+7)/2}` satisfies `p₁ = 1` dividing all eigenvalues, yet
    `amp8 1 (4m+3) (4m+5) (4m+7) (2π / (4m+5)) < 0`, hence `HasESEReal`.
  - **Theorem 7 (`odd_rupture_11x11_threshold`)**: For the `11 × 11` symmetric PST family
    `S(m) = {0, ±1, ±2m, ±(2m+1), ±(2m+2), ±(2m+3)}`:
      * Subcritical (`m ∈ {1, 2, 3, 4, 5}`, `2m ≤ 10`): NO ESE, certified by exact `DEN = 1`
        global rational Sum-of-Squares decompositions of `Q_m(cos t) = P_m(cos t) / (1 + cos t)^5`;
      * Supercritical (`∀ m ≥ 6`, `2m ≥ 12`): `amp11 < 0` at `t₀ = 2π / (4m + 3) ∈ (0, π)`.
  - **Theorem 8 (`universal_phase_transition_3R_plus_2`)**: Exact `(R, r)` Krawtchouk-core vs.
    spectral-cluster phase-transition law at `r_crit(R) = R + 1` (`N_crit(R) = 3R + 2`).
-/

@[expose] public section

open scoped BigOperators
open Finset Filter

namespace SpectralEclipse

/-! ### Theorem 5: Sharp Even Rupture Dimension `N_crit^even = 8` -/

/-- **Theorem 5 (Sharp Even Rupture at `N = 8`)**: For EVERY integer `m ≥ 1`, the `8 × 8`
symmetric PST chain `{±1/2, ±(4m+3)/2, ±(4m+5)/2, ±(4m+7)/2}` evaluates strictly negatively
at `t₀ = 2π / (4m + 5) ∈ (0, π)` and therefore exhibits Early State Exclusion. -/
theorem even_rupture_8x8 {m : ℕ} (hm : 1 ≤ m) :
    let M : ℝ := (4 * m + 5 : ℕ)
    amp8 1 (M - 2) M (M + 2) (2 * Real.pi / M) < 0 ∧
    HasESEReal (amp8 1 (M - 2) M (M + 2)) := by
  intro M
  have hM_nat : 9 ≤ 4 * m + 5 := by omega
  have hM9 : (9 : ℝ) ≤ M := by dsimp only [M]; exact_mod_cast hM_nat
  have hM0 : 0 < M := by linarith
  set d : ℝ := M - 9
  have hd : 0 ≤ d := by simp only [d]; linarith
  have hM_eq : M = d + 9 := by simp only [d]; ring
  set w1 : ℝ := 1 / (1 * ((M - 2) ^ 2 - 1 ^ 2) * (M ^ 2 - 1 ^ 2) * ((M + 2) ^ 2 - 1 ^ 2))
  set w2 : ℝ := 1 / ((M - 2) * ((M - 2) ^ 2 - 1 ^ 2) * (M ^ 2 - (M - 2) ^ 2) * ((M + 2) ^ 2 - (M - 2) ^ 2))
  set w3 : ℝ := 1 / (M * (M ^ 2 - 1 ^ 2) * (M ^ 2 - (M - 2) ^ 2) * ((M + 2) ^ 2 - M ^ 2))
  set w4 : ℝ := 1 / ((M + 2) * ((M + 2) ^ 2 - 1 ^ 2) * ((M + 2) ^ 2 - (M - 2) ^ 2) * ((M + 2) ^ 2 - M ^ 2))
  have hw1_f : w1 = 1 / ((d + 6) * (d + 8) ^ 2 * (d + 10) ^ 2 * (d + 12)) := by
    simp only [w1, hM_eq]; congr 1; ring
  have hw2_f : w2 = 1 / (32 * (d + 6) * (d + 7) * (d + 8) ^ 2 * (d + 9)) := by
    simp only [w2, hM_eq]; congr 1; ring
  have hw3_f : w3 = 1 / (16 * (d + 8) ^ 2 * (d + 9) * (d + 10) ^ 2) := by
    simp only [w3, hM_eq]; congr 1; ring
  have hw4_f : w4 = 1 / (32 * (d + 9) * (d + 10) ^ 2 * (d + 11) * (d + 12)) := by
    simp only [w4, hM_eq]; congr 1; ring
  have hw1 : 0 < w1 := by rw [hw1_f]; positivity
  have hw2 : 0 < w2 := by rw [hw2_f]; positivity
  have hw3 : 0 < w3 := by rw [hw3_f]; positivity
  have hw4 : 0 < w4 := by rw [hw4_f]; positivity
  have hden : 0 < w1 + w2 + w3 + w4 := by linarith
  set t0 : ℝ := 2 * Real.pi / M
  have ht0_pos : 0 < t0 := div_pos (by positivity) hM0
  have ht0_lt : t0 < Real.pi := by
    simp only [t0]; rw [div_lt_iff₀ hM0]; nlinarith [Real.pi_pos]
  have hc1 : Real.cos (1 * t0 / 2) ≤ 1 := Real.cos_le_one _
  have hc3 : Real.cos (M * t0 / 2) = -1 := by
    have : M * t0 / 2 = Real.pi := by simp only [t0]; field_simp [hM0.ne']
    rw [this, Real.cos_pi]
  have hc2 : Real.cos ((M - 2) * t0 / 2) = -Real.cos (2 * Real.pi / M) := by
    have : (M - 2) * t0 / 2 = Real.pi - 2 * Real.pi / M := by simp only [t0]; field_simp [hM0.ne']
    rw [this, Real.cos_pi_sub]
  have hc4 : Real.cos ((M + 2) * t0 / 2) = -Real.cos (2 * Real.pi / M) := by
    have : (M + 2) * t0 / 2 = 2 * Real.pi / M + Real.pi := by simp only [t0]; field_simp [hM0.ne']; ring
    rw [this, Real.cos_add_pi]
  have hcos_lb : 1 - 20 / M ^ 2 ≤ Real.cos (2 * Real.pi / M) := by
    have htb := one_sub_cos_le_sq_div_two (2 * Real.pi / M)
    have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
    have hpi2 : 2 * Real.pi ^ 2 < 20 := by nlinarith [Real.pi_pos]
    have hsq : (2 * Real.pi / M) ^ 2 / 2 ≤ 20 / M ^ 2 := by
      have : (2 * Real.pi / M) ^ 2 / 2 = 2 * Real.pi ^ 2 / M ^ 2 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hpi2.le (sq_nonneg M)
    linarith
  have hpoly_pos : 0 < (w2 + w4) * (1 - 20 / M ^ 2) + w3 - w1 := by
    rw [hw1_f, hw2_f, hw3_f, hw4_f, hM_eq]
    have hd6 : (0 : ℝ) < d + 6 := by linarith
    have hd7 : (0 : ℝ) < d + 7 := by linarith
    have hd8 : (0 : ℝ) < d + 8 := by linarith
    have hd9 : (0 : ℝ) < d + 9 := by linarith
    have hd10 : (0 : ℝ) < d + 10 := by linarith
    have hd11 : (0 : ℝ) < d + 11 := by linarith
    have hd12 : (0 : ℝ) < d + 12 := by linarith
    have hD_pos : 0 < 32 * (d + 6) * (d + 7) * (d + 8) ^ 2 * (d + 9) ^ 3 * (d + 10) ^ 2 *
        (d + 11) * (d + 12) := by positivity
    have hnum_pos : 0 < 71040 + 294480 * d + 147688 * d ^ 2 + 31376 * d ^ 3 +
        3388 * d ^ 4 + 184 * d ^ 5 + 4 * d ^ 6 := by
      positivity
    have hrat :
        (1 / (32 * (d + 6) * (d + 7) * (d + 8) ^ 2 * (d + 9)) +
         1 / (32 * (d + 9) * (d + 10) ^ 2 * (d + 11) * (d + 12))) * (1 - 20 / (d + 9) ^ 2) +
        1 / (16 * (d + 8) ^ 2 * (d + 9) * (d + 10) ^ 2) -
        1 / ((d + 6) * (d + 8) ^ 2 * (d + 10) ^ 2 * (d + 12)) =
        (71040 + 294480 * d + 147688 * d ^ 2 + 31376 * d ^ 3 +
          3388 * d ^ 4 + 184 * d ^ 5 + 4 * d ^ 6) /
        (32 * (d + 6) * (d + 7) * (d + 8) ^ 2 * (d + 9) ^ 3 * (d + 10) ^ 2 *
          (d + 11) * (d + 12)) := by
      field_simp [hd6.ne', hd7.ne', hd8.ne', hd9.ne', hd10.ne', hd11.ne', hd12.ne']
      ring
    rw [hrat]
    exact div_pos hnum_pos hD_pos
  have hneg : amp8 1 (M - 2) M (M + 2) t0 < 0 := by
    change (w1 * Real.cos (1 * t0 / 2) + w2 * Real.cos ((M - 2) * t0 / 2) +
      w3 * Real.cos (M * t0 / 2) + w4 * Real.cos ((M + 2) * t0 / 2)) / (w1 + w2 + w3 + w4) < 0
    refine div_neg_of_neg_of_pos ?_ hden
    rw [hc2, hc3, hc4]
    have hmul1 : w1 * Real.cos (1 * t0 / 2) ≤ w1 := by nlinarith
    have hmul24 : (w2 + w4) * (1 - 20 / M ^ 2) ≤ (w2 + w4) * Real.cos (2 * Real.pi / M) :=
      mul_le_mul_of_nonneg_left hcos_lb (by linarith)
    linarith
  have hcont : Continuous (amp8 1 (M - 2) M (M + 2)) := by unfold amp8; fun_prop
  have hA0 : 0 < amp8 1 (M - 2) M (M + 2) 0 := by
    unfold amp8
    dsimp only
    simp only [mul_zero, zero_div, Real.cos_zero, mul_one]
    have hden' : w1 + w2 + w3 + w4 ≠ 0 := hden.ne'
    change 0 < (w1 + w2 + w3 + w4) / (w1 + w2 + w3 + w4)
    rw [div_self hden']
    norm_num
  exact ⟨hneg, hasESEReal_of_pos_zero_neg_pt hcont hA0 ht0_pos ht0_lt hneg⟩

/-! ### Theorem 7: Sharp Odd Rupture Dimension `N_crit^odd = 11` & Exact Integer Threshold `M* = 12` -/

/-- Chebyshev polynomials of the first kind `T_k(x)` defined recursively for exact trigonometric
expansion `cos(k t) = T_k(cos t)`. -/
def chebT : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | n + 2, x => 2 * x * chebT (n + 1) x - chebT n x

theorem cos_nat_mul_eq_chebT (k : ℕ) (t : ℝ) : Real.cos ((k : ℝ) * t) = chebT k (Real.cos t) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [chebT]
    | 1 => simp [chebT]
    | n + 2 =>
      simp only [chebT]
      rw [← ih (n + 1) (by omega), ← ih n (by omega)]
      have h1 := Real.cos_add (((n + 1 : ℕ) : ℝ) * t) t
      have h2 := Real.cos_sub (((n + 1 : ℕ) : ℝ) * t) t
      have ha : ((n + 1 : ℕ) : ℝ) * t + t = ((n + 2 : ℕ) : ℝ) * t := by push_cast; ring
      have hb : ((n + 1 : ℕ) : ℝ) * t - t = (n : ℝ) * t := by push_cast; ring
      rw [ha] at h1
      rw [hb] at h2
      linarith

/-- Pure polynomial identity proving the `11 × 11` supercritical numerator is strictly positive
for all `d = M - 27 ≥ 0`. Extracted so `ring` runs instantaneously without `let`-bindings. -/
private theorem poly11_super_alg (d : ℝ) :
    8 * (d + 28) ^ 2 * (d + 29) * (d + 30) ^ 2 * (d + 32) * ((d + 27) ^ 2 - 45) +
    8 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 26) ^ 2 * ((d + 27) ^ 2 - 45) +
    24 * (d + 22) * (d + 24) * (d + 29) * (d + 30) ^ 2 * (d + 32) * ((d + 27) ^ 2 - 5) +
    24 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 30) * (d + 32) * ((d + 27) ^ 2 - 5) -
    768 * (d + 22) * (d + 25) * (d + 27) ^ 3 * (d + 29) * (d + 32) -
    768 * (d + 24) * (d + 25) * (d + 27) ^ 3 * (d + 29) * (d + 30) =
    2095687987200 + 1194606351360 * d + 230401317888 * d ^ 2 +
    22733214720 * d ^ 3 + 1317205120 * d ^ 4 + 46916352 * d ^ 5 +
    1015168 * d ^ 6 + 12288 * d ^ 7 + 64 * d ^ 8 := by
  ring

/-- Supercritical half of Theorem 7: For EVERY integer `m ≥ 6` (`2m ≥ 12`), the `11 × 11`
symmetric PST chain `{0, ±1, ±2m, ±(2m+1), ±(2m+2), ±(2m+3)}` evaluates strictly negatively
at `t₀ = 2π / (4m + 3) ∈ (0, π)`, hence exhibits Early State Exclusion. -/
theorem odd_rupture_11x11_supercritical {m : ℕ} (hm : 6 ≤ m) :
    let l2 : ℝ := (2 * m : ℕ)
    let l3 : ℝ := (2 * m + 1 : ℕ)
    let l4 : ℝ := (2 * m + 2 : ℕ)
    let l5 : ℝ := (2 * m + 3 : ℕ)
    amp11 1 l2 l3 l4 l5 (2 * Real.pi / ((4 * m + 3 : ℕ) : ℝ)) < 0 ∧
    HasESEReal (amp11 1 l2 l3 l4 l5) := by
  intro l2 l3 l4 l5
  set M : ℝ := ((4 * m + 3 : ℕ) : ℝ)
  have hM27 : (27 : ℝ) ≤ M := by
    simp only [M]; exact_mod_cast (show 27 ≤ 4 * m + 3 by omega)
  have hM0 : 0 < M := by linarith
  set d : ℝ := M - 27
  have hd : 0 ≤ d := by simp only [d]; linarith
  have hM_eq : M = d + 27 := by simp only [d]; ring
  have hl2_eq : l2 = (d + 24) / 2 := by simp only [l2, d, M]; push_cast; ring
  have hl3_eq : l3 = (d + 26) / 2 := by simp only [l3, d, M]; push_cast; ring
  have hl4_eq : l4 = (d + 28) / 2 := by simp only [l4, d, M]; push_cast; ring
  have hl5_eq : l5 = (d + 30) / 2 := by simp only [l5, d, M]; push_cast; ring
  set w0 : ℝ := 1 / (1 ^ 2 * l2 ^ 2 * l3 ^ 2 * l4 ^ 2 * l5 ^ 2)
  set w1 : ℝ := 1 / (1 ^ 2 * (l2 ^ 2 - 1 ^ 2) * (l3 ^ 2 - 1 ^ 2) * (l4 ^ 2 - 1 ^ 2) * (l5 ^ 2 - 1 ^ 2))
  set w2 : ℝ := 1 / (l2 ^ 2 * (l2 ^ 2 - 1 ^ 2) * (l3 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l2 ^ 2) * (l5 ^ 2 - l2 ^ 2))
  set w3 : ℝ := 1 / (l3 ^ 2 * (l3 ^ 2 - 1 ^ 2) * (l3 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l3 ^ 2))
  set w4 : ℝ := 1 / (l4 ^ 2 * (l4 ^ 2 - 1 ^ 2) * (l4 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l4 ^ 2))
  set w5 : ℝ := 1 / (l5 ^ 2 * (l5 ^ 2 - 1 ^ 2) * (l5 ^ 2 - l2 ^ 2) * (l5 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l4 ^ 2))
  have hd22 : (0 : ℝ) < d + 22 := by linarith
  have hd24 : (0 : ℝ) < d + 24 := by linarith
  have hd25 : (0 : ℝ) < d + 25 := by linarith
  have hd26 : (0 : ℝ) < d + 26 := by linarith
  have hd27 : (0 : ℝ) < d + 27 := by linarith
  have hd28 : (0 : ℝ) < d + 28 := by linarith
  have hd29 : (0 : ℝ) < d + 29 := by linarith
  have hd30 : (0 : ℝ) < d + 30 := by linarith
  have hd32 : (0 : ℝ) < d + 32 := by linarith
  have hw0_f : w0 = 256 / ((d + 24) ^ 2 * (d + 26) ^ 2 * (d + 28) ^ 2 * (d + 30) ^ 2) := by
    have hden_eq : 1 ^ 2 * l2 ^ 2 * l3 ^ 2 * l4 ^ 2 * l5 ^ 2 =
        ((d + 24) ^ 2 * (d + 26) ^ 2 * (d + 28) ^ 2 * (d + 30) ^ 2) / 256 := by
      rw [hl2_eq, hl3_eq, hl4_eq, hl5_eq]; ring
    simp only [w0, hden_eq, one_div_div]
  have hw1_f : w1 = 256 / ((d + 22) * (d + 24) * (d + 26) ^ 2 * (d + 28) ^ 2 * (d + 30) * (d + 32)) := by
    have hden_eq : 1 ^ 2 * (l2 ^ 2 - 1 ^ 2) * (l3 ^ 2 - 1 ^ 2) * (l4 ^ 2 - 1 ^ 2) * (l5 ^ 2 - 1 ^ 2) =
        ((d + 22) * (d + 24) * (d + 26) ^ 2 * (d + 28) ^ 2 * (d + 30) * (d + 32)) / 256 := by
      rw [hl2_eq, hl3_eq, hl4_eq, hl5_eq]; ring
    simp only [w1, hden_eq, one_div_div]
  have hw2_f : w2 = 8 / (3 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 26) ^ 2 * (d + 27)) := by
    have hden_eq : l2 ^ 2 * (l2 ^ 2 - 1 ^ 2) * (l3 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l2 ^ 2) * (l5 ^ 2 - l2 ^ 2) =
        (3 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 26) ^ 2 * (d + 27)) / 8 := by
      rw [hl2_eq, hl3_eq, hl4_eq, hl5_eq]; ring
    simp only [w2, hden_eq, one_div_div]
  have hw3_f : w3 = 8 / ((d + 24) * (d + 25) * (d + 26) ^ 2 * (d + 27) * (d + 28) ^ 2) := by
    have hden_eq : l3 ^ 2 * (l3 ^ 2 - 1 ^ 2) * (l3 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l3 ^ 2) =
        ((d + 24) * (d + 25) * (d + 26) ^ 2 * (d + 27) * (d + 28) ^ 2) / 8 := by
      rw [hl2_eq, hl3_eq, hl4_eq, hl5_eq]; ring
    simp only [w3, hden_eq, one_div_div]
  have hw4_f : w4 = 8 / ((d + 26) ^ 2 * (d + 27) * (d + 28) ^ 2 * (d + 29) * (d + 30)) := by
    have hden_eq : l4 ^ 2 * (l4 ^ 2 - 1 ^ 2) * (l4 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l4 ^ 2) =
        ((d + 26) ^ 2 * (d + 27) * (d + 28) ^ 2 * (d + 29) * (d + 30)) / 8 := by
      rw [hl2_eq, hl3_eq, hl4_eq, hl5_eq]; ring
    simp only [w4, hden_eq, one_div_div]
  have hw5_f : w5 = 8 / (3 * (d + 27) * (d + 28) ^ 2 * (d + 29) * (d + 30) ^ 2 * (d + 32)) := by
    have hden_eq : l5 ^ 2 * (l5 ^ 2 - 1 ^ 2) * (l5 ^ 2 - l2 ^ 2) * (l5 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l4 ^ 2) =
        (3 * (d + 27) * (d + 28) ^ 2 * (d + 29) * (d + 30) ^ 2 * (d + 32)) / 8 := by
      rw [hl2_eq, hl3_eq, hl4_eq, hl5_eq]; ring
    simp only [w5, hden_eq, one_div_div]
  have hw0 : 0 < w0 := by rw [hw0_f]; positivity
  have hw1 : 0 < w1 := by rw [hw1_f]; positivity
  have hw2 : 0 < w2 := by rw [hw2_f]; positivity
  have hw3 : 0 < w3 := by rw [hw3_f]; positivity
  have hw4 : 0 < w4 := by rw [hw4_f]; positivity
  have hw5 : 0 < w5 := by rw [hw5_f]; positivity
  have hden : 0 < w0 + w1 + w2 + w3 + w4 + w5 := by linarith
  set t0 : ℝ := 2 * Real.pi / M
  have ht0_pos : 0 < t0 := div_pos (by positivity) hM0
  have ht0_lt : t0 < Real.pi := by
    simp only [t0]; rw [div_lt_iff₀ hM0]; nlinarith [Real.pi_pos]
  have hc1 : Real.cos (1 * t0) ≤ 1 := Real.cos_le_one _
  have hc2 : Real.cos (l2 * t0) = -Real.cos (3 * Real.pi / M) := by
    have : l2 * t0 = Real.pi - 3 * Real.pi / M := by
      simp only [l2, t0, M]; push_cast; field_simp [hM0.ne']; ring
    rw [this, Real.cos_pi_sub]
  have hc3 : Real.cos (l3 * t0) = -Real.cos (Real.pi / M) := by
    have : l3 * t0 = Real.pi - Real.pi / M := by
      simp only [l3, t0, M]; push_cast; field_simp [hM0.ne']; ring
    rw [this, Real.cos_pi_sub]
  have hc4 : Real.cos (l4 * t0) = -Real.cos (Real.pi / M) := by
    have : l4 * t0 = Real.pi / M + Real.pi := by
      simp only [l4, t0, M]; push_cast; field_simp [hM0.ne']; ring
    rw [this, Real.cos_add_pi]
  have hc5 : Real.cos (l5 * t0) = -Real.cos (3 * Real.pi / M) := by
    have : l5 * t0 = 3 * Real.pi / M + Real.pi := by
      simp only [l5, t0, M]; push_cast; field_simp [hM0.ne']; ring
    rw [this, Real.cos_add_pi]
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have hcos_lb1 : 1 - 5 / M ^ 2 ≤ Real.cos (Real.pi / M) := by
    have htb := one_sub_cos_le_sq_div_two (Real.pi / M)
    have hpi2 : Real.pi ^ 2 / 2 < 5 := by nlinarith only [Real.pi_pos, hpi_lt]
    have hsq : (Real.pi / M) ^ 2 / 2 ≤ 5 / M ^ 2 := by
      have : (Real.pi / M) ^ 2 / 2 = (Real.pi ^ 2 / 2) / M ^ 2 := by ring
      rw [this]; exact div_le_div_of_nonneg_right hpi2.le (sq_nonneg M)
    linarith only [htb, hsq]
  have hcos_lb3 : 1 - 45 / M ^ 2 ≤ Real.cos (3 * Real.pi / M) := by
    have htb := one_sub_cos_le_sq_div_two (3 * Real.pi / M)
    have hpi2 : 9 * Real.pi ^ 2 / 2 < 45 := by nlinarith only [Real.pi_pos, hpi_lt]
    have hsq : (3 * Real.pi / M) ^ 2 / 2 ≤ 45 / M ^ 2 := by
      have : (3 * Real.pi / M) ^ 2 / 2 = (9 * Real.pi ^ 2 / 2) / M ^ 2 := by ring
      rw [this]; exact div_le_div_of_nonneg_right hpi2.le (sq_nonneg M)
    linarith only [htb, hsq]
  have hpoly_pos : 0 < (w2 + w5) * (1 - 45 / M ^ 2) + (w3 + w4) * (1 - 5 / M ^ 2) - w0 - w1 := by
    set D : ℝ := 3 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 26) ^ 2 * (d + 27) ^ 3 *
      (d + 28) ^ 2 * (d + 29) * (d + 30) ^ 2 * (d + 32)
    have hD_pos : 0 < D := by positivity
    have hDw0 : D * w0 = 768 * (d + 22) * (d + 25) * (d + 27) ^ 3 * (d + 29) * (d + 32) := by
      rw [hw0_f]; simp only [D]; field_simp [hd24.ne', hd26.ne', hd28.ne', hd30.ne']; ring
    have hDw1 : D * w1 = 768 * (d + 24) * (d + 25) * (d + 27) ^ 3 * (d + 29) * (d + 30) := by
      rw [hw1_f]; simp only [D]; field_simp [hd22.ne', hd24.ne', hd26.ne', hd28.ne', hd30.ne', hd32.ne']; ring
    have hDw2 : D * (w2 * (1 - 45 / M ^ 2)) =
        8 * (d + 28) ^ 2 * (d + 29) * (d + 30) ^ 2 * (d + 32) * ((d + 27) ^ 2 - 45) := by
      rw [hw2_f, hM_eq]; simp only [D]
      field_simp [hd22.ne', hd24.ne', hd25.ne', hd26.ne', hd27.ne']
    have hDw5 : D * (w5 * (1 - 45 / M ^ 2)) =
        8 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 26) ^ 2 * ((d + 27) ^ 2 - 45) := by
      rw [hw5_f, hM_eq]; simp only [D]
      field_simp [hd27.ne', hd28.ne', hd29.ne', hd30.ne', hd32.ne']
    have hDw3 : D * (w3 * (1 - 5 / M ^ 2)) =
        24 * (d + 22) * (d + 24) * (d + 29) * (d + 30) ^ 2 * (d + 32) * ((d + 27) ^ 2 - 5) := by
      rw [hw3_f, hM_eq]; simp only [D]
      field_simp [hd24.ne', hd25.ne', hd26.ne', hd27.ne', hd28.ne']; ring
    have hDw4 : D * (w4 * (1 - 5 / M ^ 2)) =
        24 * (d + 22) * (d + 24) ^ 2 * (d + 25) * (d + 30) * (d + 32) * ((d + 27) ^ 2 - 5) := by
      rw [hw4_f, hM_eq]; simp only [D]
      field_simp [hd26.ne', hd27.ne', hd28.ne', hd29.ne', hd30.ne']; ring
    have hD_prod :
        D * ((w2 + w5) * (1 - 45 / M ^ 2) + (w3 + w4) * (1 - 5 / M ^ 2) - w0 - w1) =
        2095687987200 + 1194606351360 * d + 230401317888 * d ^ 2 +
        22733214720 * d ^ 3 + 1317205120 * d ^ 4 + 46916352 * d ^ 5 +
        1015168 * d ^ 6 + 12288 * d ^ 7 + 64 * d ^ 8 := by
      have hlin : D * ((w2 + w5) * (1 - 45 / M ^ 2) + (w3 + w4) * (1 - 5 / M ^ 2) - w0 - w1) =
          D * (w2 * (1 - 45 / M ^ 2)) + D * (w5 * (1 - 45 / M ^ 2)) +
          D * (w3 * (1 - 5 / M ^ 2)) + D * (w4 * (1 - 5 / M ^ 2)) - D * w0 - D * w1 := by ring
      rw [hlin, hDw0, hDw1, hDw2, hDw3, hDw4, hDw5]
      exact poly11_super_alg d
    have hnum_pos : 0 < 2095687987200 + 1194606351360 * d + 230401317888 * d ^ 2 +
        22733214720 * d ^ 3 + 1317205120 * d ^ 4 + 46916352 * d ^ 5 +
        1015168 * d ^ 6 + 12288 * d ^ 7 + 64 * d ^ 8 := by positivity
    by_contra hle
    push Not at hle
    have hnonpos : D * ((w2 + w5) * (1 - 45 / M ^ 2) + (w3 + w4) * (1 - 5 / M ^ 2) - w0 - w1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD_pos.le hle
    linarith
  have hneg : amp11 1 l2 l3 l4 l5 t0 < 0 := by
    change (w0 + w1 * Real.cos (1 * t0) + w2 * Real.cos (l2 * t0) + w3 * Real.cos (l3 * t0) +
      w4 * Real.cos (l4 * t0) + w5 * Real.cos (l5 * t0)) / (w0 + w1 + w2 + w3 + w4 + w5) < 0
    refine div_neg_of_neg_of_pos ?_ hden
    rw [hc2, hc3, hc4, hc5]
    have hm1 : w1 * Real.cos (1 * t0) ≤ w1 := mul_le_of_le_one_right hw1.le hc1
    have hm25 : (w2 + w5) * (1 - 45 / M ^ 2) ≤ (w2 + w5) * Real.cos (3 * Real.pi / M) :=
      mul_le_mul_of_nonneg_left hcos_lb3 (by linarith only [hw2, hw5])
    have hm34 : (w3 + w4) * (1 - 5 / M ^ 2) ≤ (w3 + w4) * Real.cos (Real.pi / M) :=
      mul_le_mul_of_nonneg_left hcos_lb1 (by linarith only [hw3, hw4])
    linarith only [hm1, hm25, hm34, hpoly_pos]
  have hcont : Continuous (amp11 1 l2 l3 l4 l5) := by unfold amp11; fun_prop
  have hA0 : 0 < amp11 1 l2 l3 l4 l5 0 := by
    unfold amp11; dsimp only
    simp only [mul_zero, Real.cos_zero, mul_one]
    change 0 < (w0 + w1 + w2 + w3 + w4 + w5) / (w0 + w1 + w2 + w3 + w4 + w5)
    rw [div_self hden.ne']
    norm_num
  exact ⟨hneg, hasESEReal_of_pos_zero_neg_pt hcont hA0 ht0_pos ht0_lt hneg⟩

private theorem amp11_sub_m1 {τ : ℝ} (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    0 < amp11 1 2 3 4 5 τ := by
  set x : ℝ := Real.cos τ
  have h1px : 0 < 1 + x := by
    have h1 := Real.strictAntiOn_cos ⟨hτ0.le, hτpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hτpi
    rw [Real.cos_pi] at h1; simp only [x]; linarith
  have hcs1 : Real.cos (1 * τ) = chebT 1 x := by simpa using cos_nat_mul_eq_chebT 1 τ
  have hcs2 : Real.cos (2 * τ) = chebT 2 x := by simpa using cos_nat_mul_eq_chebT 2 τ
  have hcs3 : Real.cos (3 * τ) = chebT 3 x := by simpa using cos_nat_mul_eq_chebT 3 τ
  have hcs4 : Real.cos (4 * τ) = chebT 4 x := by simpa using cos_nat_mul_eq_chebT 4 τ
  have hcs5 : Real.cos (5 * τ) = chebT 5 x := by simpa using cos_nat_mul_eq_chebT 5 τ
  unfold amp11; dsimp only
  rw [hcs1, hcs2, hcs3, hcs4, hcs5]
  have heq : (1 / (1 ^ 2 * 2 ^ 2 * 3 ^ 2 * 4 ^ 2 * 5 ^ 2) +
      1 / (1 ^ 2 * (2 ^ 2 - 1 ^ 2) * (3 ^ 2 - 1 ^ 2) * (4 ^ 2 - 1 ^ 2) * (5 ^ 2 - 1 ^ 2)) * chebT 1 x +
      1 / (2 ^ 2 * (2 ^ 2 - 1 ^ 2) * (3 ^ 2 - 2 ^ 2) * (4 ^ 2 - 2 ^ 2) * (5 ^ 2 - 2 ^ 2)) * chebT 2 x +
      1 / (3 ^ 2 * (3 ^ 2 - 1 ^ 2) * (3 ^ 2 - 2 ^ 2) * (4 ^ 2 - 3 ^ 2) * (5 ^ 2 - 3 ^ 2)) * chebT 3 x +
      1 / (4 ^ 2 * (4 ^ 2 - 1 ^ 2) * (4 ^ 2 - 2 ^ 2) * (4 ^ 2 - 3 ^ 2) * (5 ^ 2 - 4 ^ 2)) * chebT 4 x +
      1 / (5 ^ 2 * (5 ^ 2 - 1 ^ 2) * (5 ^ 2 - 2 ^ 2) * (5 ^ 2 - 3 ^ 2) * (5 ^ 2 - 4 ^ 2)) * chebT 5 x) /
      (1 / (1 ^ 2 * 2 ^ 2 * 3 ^ 2 * 4 ^ 2 * 5 ^ 2) +
       1 / (1 ^ 2 * (2 ^ 2 - 1 ^ 2) * (3 ^ 2 - 1 ^ 2) * (4 ^ 2 - 1 ^ 2) * (5 ^ 2 - 1 ^ 2)) +
       1 / (2 ^ 2 * (2 ^ 2 - 1 ^ 2) * (3 ^ 2 - 2 ^ 2) * (4 ^ 2 - 2 ^ 2) * (5 ^ 2 - 2 ^ 2)) +
       1 / (3 ^ 2 * (3 ^ 2 - 1 ^ 2) * (3 ^ 2 - 2 ^ 2) * (4 ^ 2 - 3 ^ 2) * (5 ^ 2 - 3 ^ 2)) +
       1 / (4 ^ 2 * (4 ^ 2 - 1 ^ 2) * (4 ^ 2 - 2 ^ 2) * (4 ^ 2 - 3 ^ 2) * (5 ^ 2 - 4 ^ 2)) +
       1 / (5 ^ 2 * (5 ^ 2 - 1 ^ 2) * (5 ^ 2 - 2 ^ 2) * (5 ^ 2 - 3 ^ 2) * (5 ^ 2 - 4 ^ 2))) =
      (1 + x) ^ 5 / 32 := by simp only [chebT]; ring
  rw [heq]; positivity

private theorem amp11_sub_m2 {τ : ℝ} (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    0 < amp11 1 4 5 6 7 τ := by
  set x : ℝ := Real.cos τ
  have h1px : 0 < 1 + x := by
    have h1 := Real.strictAntiOn_cos ⟨hτ0.le, hτpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hτpi
    rw [Real.cos_pi] at h1; simp only [x]; linarith
  have hcs1 : Real.cos (1 * τ) = chebT 1 x := by simpa using cos_nat_mul_eq_chebT 1 τ
  have hcs4 : Real.cos (4 * τ) = chebT 4 x := by simpa using cos_nat_mul_eq_chebT 4 τ
  have hcs5 : Real.cos (5 * τ) = chebT 5 x := by simpa using cos_nat_mul_eq_chebT 5 τ
  have hcs6 : Real.cos (6 * τ) = chebT 6 x := by simpa using cos_nat_mul_eq_chebT 6 τ
  have hcs7 : Real.cos (7 * τ) = chebT 7 x := by simpa using cos_nat_mul_eq_chebT 7 τ
  unfold amp11; dsimp only
  rw [hcs1, hcs4, hcs5, hcs6, hcs7]
  have hQ : 0 < 209 - 492 * x + 300 * x ^ 2 := by
    have hsos : 209 - 492 * x + 300 * x ^ 2 =
        209 * (1 - 246 / 209 * x) ^ 2 + 2184 / 209 * x ^ 2 := by ring
    rw [hsos]
    by_cases hx : x = 0
    · rw [hx]; norm_num
    · positivity
  have heq : (1 / (1 ^ 2 * 4 ^ 2 * 5 ^ 2 * 6 ^ 2 * 7 ^ 2) +
      1 / (1 ^ 2 * (4 ^ 2 - 1 ^ 2) * (5 ^ 2 - 1 ^ 2) * (6 ^ 2 - 1 ^ 2) * (7 ^ 2 - 1 ^ 2)) * chebT 1 x +
      1 / (4 ^ 2 * (4 ^ 2 - 1 ^ 2) * (5 ^ 2 - 4 ^ 2) * (6 ^ 2 - 4 ^ 2) * (7 ^ 2 - 4 ^ 2)) * chebT 4 x +
      1 / (5 ^ 2 * (5 ^ 2 - 1 ^ 2) * (5 ^ 2 - 4 ^ 2) * (6 ^ 2 - 5 ^ 2) * (7 ^ 2 - 5 ^ 2)) * chebT 5 x +
      1 / (6 ^ 2 * (6 ^ 2 - 1 ^ 2) * (6 ^ 2 - 4 ^ 2) * (6 ^ 2 - 5 ^ 2) * (7 ^ 2 - 6 ^ 2)) * chebT 6 x +
      1 / (7 ^ 2 * (7 ^ 2 - 1 ^ 2) * (7 ^ 2 - 4 ^ 2) * (7 ^ 2 - 5 ^ 2) * (7 ^ 2 - 6 ^ 2)) * chebT 7 x) /
      (1 / (1 ^ 2 * 4 ^ 2 * 5 ^ 2 * 6 ^ 2 * 7 ^ 2) +
       1 / (1 ^ 2 * (4 ^ 2 - 1 ^ 2) * (5 ^ 2 - 1 ^ 2) * (6 ^ 2 - 1 ^ 2) * (7 ^ 2 - 1 ^ 2)) +
       1 / (4 ^ 2 * (4 ^ 2 - 1 ^ 2) * (5 ^ 2 - 4 ^ 2) * (6 ^ 2 - 4 ^ 2) * (7 ^ 2 - 4 ^ 2)) +
       1 / (5 ^ 2 * (5 ^ 2 - 1 ^ 2) * (5 ^ 2 - 4 ^ 2) * (6 ^ 2 - 5 ^ 2) * (7 ^ 2 - 5 ^ 2)) +
       1 / (6 ^ 2 * (6 ^ 2 - 1 ^ 2) * (6 ^ 2 - 4 ^ 2) * (6 ^ 2 - 5 ^ 2) * (7 ^ 2 - 6 ^ 2)) +
       1 / (7 ^ 2 * (7 ^ 2 - 1 ^ 2) * (7 ^ 2 - 4 ^ 2) * (7 ^ 2 - 5 ^ 2) * (7 ^ 2 - 6 ^ 2))) =
      (1 + x) ^ 5 * (209 - 492 * x + 300 * x ^ 2) / 544 := by simp only [chebT]; ring
  rw [heq]; positivity

private theorem amp11_sub_m3 {τ : ℝ} (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    0 < amp11 1 6 7 8 9 τ := by
  set x : ℝ := Real.cos τ
  have h1px : 0 < 1 + x := by
    have h1 := Real.strictAntiOn_cos ⟨hτ0.le, hτpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hτpi
    rw [Real.cos_pi] at h1; simp only [x]; linarith
  have hcs1 : Real.cos (1 * τ) = chebT 1 x := by simpa using cos_nat_mul_eq_chebT 1 τ
  have hcs6 : Real.cos (6 * τ) = chebT 6 x := by simpa using cos_nat_mul_eq_chebT 6 τ
  have hcs7 : Real.cos (7 * τ) = chebT 7 x := by simpa using cos_nat_mul_eq_chebT 7 τ
  have hcs8 : Real.cos (8 * τ) = chebT 8 x := by simpa using cos_nat_mul_eq_chebT 8 τ
  have hcs9 : Real.cos (9 * τ) = chebT 9 x := by simpa using cos_nat_mul_eq_chebT 9 τ
  unfold amp11; dsimp only
  rw [hcs1, hcs6, hcs7, hcs8, hcs9]
  have hQ : 0 < 151 - 1232 * x + 4272 * x ^ 2 - 5720 * x ^ 3 + 2548 * x ^ 4 := by
    have hsos : 151 - 1232 * x + 4272 * x ^ 2 - 5720 * x ^ 3 + 2548 * x ^ 4 =
        151 * (1 - 616 / 151 * x + 493 / 151 * x ^ 2) ^ 2 +
        116730 / 151 * (x - 21362 / 19455 * x ^ 2) ^ 2 +
        41377 / 6485 * (x ^ 2) ^ 2 := by ring
    rw [hsos]
    by_cases hx : x = 0
    · rw [hx]; norm_num
    · positivity
  have heq : (1 / (1 ^ 2 * 6 ^ 2 * 7 ^ 2 * 8 ^ 2 * 9 ^ 2) +
      1 / (1 ^ 2 * (6 ^ 2 - 1 ^ 2) * (7 ^ 2 - 1 ^ 2) * (8 ^ 2 - 1 ^ 2) * (9 ^ 2 - 1 ^ 2)) * chebT 1 x +
      1 / (6 ^ 2 * (6 ^ 2 - 1 ^ 2) * (7 ^ 2 - 6 ^ 2) * (8 ^ 2 - 6 ^ 2) * (9 ^ 2 - 6 ^ 2)) * chebT 6 x +
      1 / (7 ^ 2 * (7 ^ 2 - 1 ^ 2) * (7 ^ 2 - 6 ^ 2) * (8 ^ 2 - 7 ^ 2) * (9 ^ 2 - 7 ^ 2)) * chebT 7 x +
      1 / (8 ^ 2 * (8 ^ 2 - 1 ^ 2) * (8 ^ 2 - 6 ^ 2) * (8 ^ 2 - 7 ^ 2) * (9 ^ 2 - 8 ^ 2)) * chebT 8 x +
      1 / (9 ^ 2 * (9 ^ 2 - 1 ^ 2) * (9 ^ 2 - 6 ^ 2) * (9 ^ 2 - 7 ^ 2) * (9 ^ 2 - 8 ^ 2)) * chebT 9 x) /
      (1 / (1 ^ 2 * 6 ^ 2 * 7 ^ 2 * 8 ^ 2 * 9 ^ 2) +
       1 / (1 ^ 2 * (6 ^ 2 - 1 ^ 2) * (7 ^ 2 - 1 ^ 2) * (8 ^ 2 - 1 ^ 2) * (9 ^ 2 - 1 ^ 2)) +
       1 / (6 ^ 2 * (6 ^ 2 - 1 ^ 2) * (7 ^ 2 - 6 ^ 2) * (8 ^ 2 - 6 ^ 2) * (9 ^ 2 - 6 ^ 2)) +
       1 / (7 ^ 2 * (7 ^ 2 - 1 ^ 2) * (7 ^ 2 - 6 ^ 2) * (8 ^ 2 - 7 ^ 2) * (9 ^ 2 - 7 ^ 2)) +
       1 / (8 ^ 2 * (8 ^ 2 - 1 ^ 2) * (8 ^ 2 - 6 ^ 2) * (8 ^ 2 - 7 ^ 2) * (9 ^ 2 - 8 ^ 2)) +
       1 / (9 ^ 2 * (9 ^ 2 - 1 ^ 2) * (9 ^ 2 - 6 ^ 2) * (9 ^ 2 - 7 ^ 2) * (9 ^ 2 - 8 ^ 2))) =
      (1 + x) ^ 5 * (151 - 1232 * x + 4272 * x ^ 2 - 5720 * x ^ 3 + 2548 * x ^ 4) / 608 := by
    simp only [chebT]; ring
  rw [heq]; positivity

private theorem amp11_sub_m4 {τ : ℝ} (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    0 < amp11 1 8 9 10 11 τ := by
  set x : ℝ := Real.cos τ
  have h1px : 0 < 1 + x := by
    have h1 := Real.strictAntiOn_cos ⟨hτ0.le, hτpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hτpi
    rw [Real.cos_pi] at h1; simp only [x]; linarith
  have hcs1 : Real.cos (1 * τ) = chebT 1 x := by simpa using cos_nat_mul_eq_chebT 1 τ
  have hcs8 : Real.cos (8 * τ) = chebT 8 x := by simpa using cos_nat_mul_eq_chebT 8 τ
  have hcs9 : Real.cos (9 * τ) = chebT 9 x := by simpa using cos_nat_mul_eq_chebT 9 τ
  have hcs10 : Real.cos (10 * τ) = chebT 10 x := by simpa using cos_nat_mul_eq_chebT 10 τ
  have hcs11 : Real.cos (11 * τ) = chebT 11 x := by simpa using cos_nat_mul_eq_chebT 11 τ
  unfold amp11; dsimp only
  rw [hcs1, hcs8, hcs9, hcs10, hcs11]
  have hQ : 0 < 213 + 376 * x - 2360 * x ^ 2 - 8940 * x ^ 3 +
      41200 * x ^ 4 - 50048 * x ^ 5 + 19584 * x ^ 6 := by
    have hsos : 213 + 376 * x - 2360 * x ^ 2 - 8940 * x ^ 3 +
        41200 * x ^ 4 - 50048 * x ^ 5 + 19584 * x ^ 6 =
        213 * (1 + 188 / 213 * x - 2012 / 213 * x ^ 2 + 556 / 71 * x ^ 3) ^ 2 +
        319088 / 213 * (x - 9481 / 3256 * x ^ 2 + 625533 / 319088 * x ^ 3) ^ 2 +
        1098379 / 1628 * (x ^ 2 - 2333231 / 2196758 * x ^ 3) ^ 2 +
        389170541 / 107641142 * (x ^ 3) ^ 2 := by ring
    rw [hsos]
    by_cases hx : x = 0
    · rw [hx]; norm_num
    · positivity
  have heq : (1 / (1 ^ 2 * 8 ^ 2 * 9 ^ 2 * 10 ^ 2 * 11 ^ 2) +
      1 / (1 ^ 2 * (8 ^ 2 - 1 ^ 2) * (9 ^ 2 - 1 ^ 2) * (10 ^ 2 - 1 ^ 2) * (11 ^ 2 - 1 ^ 2)) * chebT 1 x +
      1 / (8 ^ 2 * (8 ^ 2 - 1 ^ 2) * (9 ^ 2 - 8 ^ 2) * (10 ^ 2 - 8 ^ 2) * (11 ^ 2 - 8 ^ 2)) * chebT 8 x +
      1 / (9 ^ 2 * (9 ^ 2 - 1 ^ 2) * (9 ^ 2 - 8 ^ 2) * (10 ^ 2 - 9 ^ 2) * (11 ^ 2 - 9 ^ 2)) * chebT 9 x +
      1 / (10 ^ 2 * (10 ^ 2 - 1 ^ 2) * (10 ^ 2 - 8 ^ 2) * (10 ^ 2 - 9 ^ 2) * (11 ^ 2 - 10 ^ 2)) * chebT 10 x +
      1 / (11 ^ 2 * (11 ^ 2 - 1 ^ 2) * (11 ^ 2 - 8 ^ 2) * (11 ^ 2 - 9 ^ 2) * (11 ^ 2 - 10 ^ 2)) * chebT 11 x) /
      (1 / (1 ^ 2 * 8 ^ 2 * 9 ^ 2 * 10 ^ 2 * 11 ^ 2) +
       1 / (1 ^ 2 * (8 ^ 2 - 1 ^ 2) * (9 ^ 2 - 1 ^ 2) * (10 ^ 2 - 1 ^ 2) * (11 ^ 2 - 1 ^ 2)) +
       1 / (8 ^ 2 * (8 ^ 2 - 1 ^ 2) * (9 ^ 2 - 8 ^ 2) * (10 ^ 2 - 8 ^ 2) * (11 ^ 2 - 8 ^ 2)) +
       1 / (9 ^ 2 * (9 ^ 2 - 1 ^ 2) * (9 ^ 2 - 8 ^ 2) * (10 ^ 2 - 9 ^ 2) * (11 ^ 2 - 9 ^ 2)) +
       1 / (10 ^ 2 * (10 ^ 2 - 1 ^ 2) * (10 ^ 2 - 8 ^ 2) * (10 ^ 2 - 9 ^ 2) * (11 ^ 2 - 10 ^ 2)) +
       1 / (11 ^ 2 * (11 ^ 2 - 1 ^ 2) * (11 ^ 2 - 8 ^ 2) * (11 ^ 2 - 9 ^ 2) * (11 ^ 2 - 10 ^ 2))) =
      (1 + x) ^ 5 * (213 + 376 * x - 2360 * x ^ 2 - 8940 * x ^ 3 +
        41200 * x ^ 4 - 50048 * x ^ 5 + 19584 * x ^ 6) / 800 := by
    simp only [chebT]; ring
  rw [heq]; positivity

private theorem amp11_sub_m5 {τ : ℝ} (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    0 < amp11 1 10 11 12 13 τ := by
  set x : ℝ := Real.cos τ
  have h1px : 0 < 1 + x := by
    have h1 := Real.strictAntiOn_cos ⟨hτ0.le, hτpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hτpi
    rw [Real.cos_pi] at h1; simp only [x]; linarith
  have hcs1 : Real.cos (1 * τ) = chebT 1 x := by simpa using cos_nat_mul_eq_chebT 1 τ
  have hcs10 : Real.cos (10 * τ) = chebT 10 x := by simpa using cos_nat_mul_eq_chebT 10 τ
  have hcs11 : Real.cos (11 * τ) = chebT 11 x := by simpa using cos_nat_mul_eq_chebT 11 τ
  have hcs12 : Real.cos (12 * τ) = chebT 12 x := by simpa using cos_nat_mul_eq_chebT 12 τ
  have hcs13 : Real.cos (13 * τ) = chebT 13 x := by simpa using cos_nat_mul_eq_chebT 13 τ
  unfold amp11; dsimp only
  rw [hcs1, hcs10, hcs11, hcs12, hcs13]
  have hQ : 0 < 199 - 2256 * x + 6144 * x ^ 2 + 16448 * x ^ 3 - 69920 * x ^ 4 +
      5632 * x ^ 5 + 205824 * x ^ 6 - 254976 * x ^ 7 + 92928 * x ^ 8 := by
    have hsos : 199 - 2256 * x + 6144 * x ^ 2 + 16448 * x ^ 3 - 69920 * x ^ 4 +
        5632 * x ^ 5 + 205824 * x ^ 6 - 254976 * x ^ 7 + 92928 * x ^ 8 =
        199 * (1 - 1128 / 199 * x - 609 / 199 * x ^ 2 + 5384 / 199 * x ^ 3 - 3906 / 199 * x ^ 4) ^ 2 +
        192654 / 199 * (x - 5536 / 8757 * x ^ 2 - 30311 / 9174 * x ^ 3 + 82399 / 27522 * x ^ 4) ^ 2 +
        26931011 / 8757 * (x ^ 2 - 68028387 / 26931011 * x ^ 3 + 41602834 / 26931011 * x ^ 4) ^ 2 +
        131950826841 / 592482242 * (x ^ 3 - 137986787905 / 131950826841 * x ^ 4) ^ 2 +
        17484878347 / 131950826841 * (x ^ 4) ^ 2 := by ring
    rw [hsos]
    by_cases hx : x = 0
    · rw [hx]; norm_num
    · positivity
  have heq : (1 / (1 ^ 2 * 10 ^ 2 * 11 ^ 2 * 12 ^ 2 * 13 ^ 2) +
      1 / (1 ^ 2 * (10 ^ 2 - 1 ^ 2) * (11 ^ 2 - 1 ^ 2) * (12 ^ 2 - 1 ^ 2) * (13 ^ 2 - 1 ^ 2)) * chebT 1 x +
      1 / (10 ^ 2 * (10 ^ 2 - 1 ^ 2) * (11 ^ 2 - 10 ^ 2) * (12 ^ 2 - 10 ^ 2) * (13 ^ 2 - 10 ^ 2)) * chebT 10 x +
      1 / (11 ^ 2 * (11 ^ 2 - 1 ^ 2) * (11 ^ 2 - 10 ^ 2) * (12 ^ 2 - 11 ^ 2) * (13 ^ 2 - 11 ^ 2)) * chebT 11 x +
      1 / (12 ^ 2 * (12 ^ 2 - 1 ^ 2) * (12 ^ 2 - 10 ^ 2) * (12 ^ 2 - 11 ^ 2) * (13 ^ 2 - 12 ^ 2)) * chebT 12 x +
      1 / (13 ^ 2 * (13 ^ 2 - 1 ^ 2) * (13 ^ 2 - 10 ^ 2) * (13 ^ 2 - 11 ^ 2) * (13 ^ 2 - 12 ^ 2)) * chebT 13 x) /
      (1 / (1 ^ 2 * 10 ^ 2 * 11 ^ 2 * 12 ^ 2 * 13 ^ 2) +
       1 / (1 ^ 2 * (10 ^ 2 - 1 ^ 2) * (11 ^ 2 - 1 ^ 2) * (12 ^ 2 - 1 ^ 2) * (13 ^ 2 - 1 ^ 2)) +
       1 / (10 ^ 2 * (10 ^ 2 - 1 ^ 2) * (11 ^ 2 - 10 ^ 2) * (12 ^ 2 - 10 ^ 2) * (13 ^ 2 - 10 ^ 2)) +
       1 / (11 ^ 2 * (11 ^ 2 - 1 ^ 2) * (11 ^ 2 - 10 ^ 2) * (12 ^ 2 - 11 ^ 2) * (13 ^ 2 - 11 ^ 2)) +
       1 / (12 ^ 2 * (12 ^ 2 - 1 ^ 2) * (12 ^ 2 - 10 ^ 2) * (12 ^ 2 - 11 ^ 2) * (13 ^ 2 - 12 ^ 2)) +
       1 / (13 ^ 2 * (13 ^ 2 - 1 ^ 2) * (13 ^ 2 - 10 ^ 2) * (13 ^ 2 - 11 ^ 2) * (13 ^ 2 - 12 ^ 2))) =
      (1 + x) ^ 5 * (199 - 2256 * x + 6144 * x ^ 2 + 16448 * x ^ 3 - 69920 * x ^ 4 +
        5632 * x ^ 5 + 205824 * x ^ 6 - 254976 * x ^ 7 + 92928 * x ^ 8) / 736 := by
    simp only [chebT]; ring
  rw [heq]; positivity

/-- Subcritical half of Theorem 7: For EVERY `m ∈ {1, 2, 3, 4, 5}` (`2m ≤ 10`), the `11 × 11`
symmetric PST chain `{0, ±1, ±2m, ±(2m+1), ±(2m+2), ±(2m+3)}` avoids Early State Exclusion. -/
theorem odd_rupture_11x11_subcritical (m : ℕ) (hm1 : 1 ≤ m) (hm5 : m ≤ 5) :
    ¬HasESEReal (amp11 1 (2 * m : ℕ) (2 * m + 1 : ℕ) (2 * m + 2 : ℕ) (2 * m + 3 : ℕ)) := by
  rintro ⟨τ, hτ0, hτpi, hzero⟩
  interval_cases m
  · have hp := amp11_sub_m1 hτ0 hτpi; norm_num at hzero; linarith
  · have hp := amp11_sub_m2 hτ0 hτpi; norm_num at hzero; linarith
  · have hp := amp11_sub_m3 hτ0 hτpi; norm_num at hzero; linarith
  · have hp := amp11_sub_m4 hτ0 hτpi; norm_num at hzero; linarith
  · have hp := amp11_sub_m5 hτ0 hτpi; norm_num at hzero; linarith

/-- **Theorem 7 (Complete `11 × 11` Exact Integer Threshold `M* = 12`)**:
For every `m ≥ 1`, the `11 × 11` symmetric PST chain `{0, ±1, ±2m, ±(2m+1), ±(2m+2), ±(2m+3)}`
has Early State Exclusion if and only if `m ≥ 6` (equivalently cluster onset `2m ≥ 12`). -/
theorem odd_rupture_11x11_threshold {m : ℕ} (hm : 1 ≤ m) :
    HasESEReal (amp11 1 (2 * m : ℕ) (2 * m + 1 : ℕ) (2 * m + 2 : ℕ) (2 * m + 3 : ℕ)) ↔ 6 ≤ m := by
  constructor
  · intro hese
    by_contra hlt
    have hm5 : m ≤ 5 := by omega
    exact odd_rupture_11x11_subcritical m hm hm5 hese
  · intro hm6
    exact (odd_rupture_11x11_supercritical hm6).2

/-! ### Theorem 8: Universal `(R, r)` Phase-Transition Law `N_crit(R) = 3R + 2` -/

/-- Exact leading cluster-to-core Hochstadt weight ratio for an `R`-eigenvalue equidistant
Krawtchouk core (`R ≥ 2`) fused with a symmetric `r`-pair unit-spaced cluster at scale `M`:
  `Φ(R, r, M) = ((R - 1)! / ((r - 1)! * 2^(R - 1))) * M^(r - R)`. -/
noncomputable def clusterToCoreRatio (R r : ℕ) (M : ℝ) : ℝ :=
  (((R - 1).factorial : ℝ) / (((r - 1).factorial : ℝ) * (2 : ℝ) ^ (R - 1))) *
    M ^ ((r : ℤ) - (R : ℤ))

/-- Exact combinatorial identity: sum of reciprocals of unit-spaced cluster self-gaps
`∑_{j=0}^{r-1} 1 / (j! * (r - 1 - j)!) = 2^(r - 1) / (r - 1)!`. -/
theorem cluster_self_gap_sum (r : ℕ) (hr : 1 ≤ r) :
    ∑ j ∈ Finset.range r, (1 : ℝ) / (((j.factorial : ℝ) * ((r - 1 - j).factorial : ℝ))) =
      (2 : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hfac : ((m.factorial : ℝ)) ≠ 0 := by positivity
  rw [eq_div_iff hfac, Finset.sum_mul]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (1 : ℝ) / ((j.factorial : ℝ) * ((m - j).factorial : ℝ)) * (m.factorial : ℝ) =
        ((Nat.choose m j : ℕ) : ℝ) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hch := Nat.choose_mul_factorial_mul_factorial hjm
    have hch_r : ((Nat.choose m j : ℕ) : ℝ) * (j.factorial : ℝ) * ((m - j).factorial : ℝ) =
        (m.factorial : ℝ) := by exact_mod_cast hch
    have hf1 : (j.factorial : ℝ) ≠ 0 := by positivity
    have hf2 : ((m - j).factorial : ℝ) ≠ 0 := by positivity
    field_simp [hf1, hf2]
    linarith
  rw [Finset.sum_congr rfl hterm]
  have hbin : ∑ j ∈ Finset.range (m + 1), Nat.choose m j = 2 ^ m := Nat.sum_range_choose m
  exact_mod_cast hbin

/-- **Theorem 8 (Universal `(R, r)` Krawtchouk-Core vs. Spectral-Cluster Phase-Transition Law)**:
For EVERY Krawtchouk core size `R ≥ 2` and symmetric `r`-pair cluster (`r ≥ 1`, chain length
`N = R + 2r`), the exact cluster-to-core asymptotic amplitude ratio `Φ(R, r, M)` satisfies the
sharp three-regime phase transition at `r_crit(R) = R + 1` (`N_crit(R) = 3R + 2`). -/
theorem universal_phase_transition_3R_plus_2 {R : ℕ} (hR : 2 ≤ R) :
    (∀ r : ℕ, 1 ≤ r → r < R →
      Tendsto (clusterToCoreRatio R r) atTop (nhds 0)) ∧
    (∀ M : ℝ, 0 < M →
      clusterToCoreRatio R R M = (2 : ℝ) ^ (-(R - 1 : ℤ)) ∧
      clusterToCoreRatio R R M ≤ 1 / 2) ∧
    (∀ r : ℕ, R + 1 ≤ r →
      Tendsto (clusterToCoreRatio R r) atTop atTop) ∧
    (∀ M : ℝ, 0 < M →
      clusterToCoreRatio R (R + 1) M = M / ((R : ℝ) * (2 : ℝ) ^ (R - 1))) ∧
    ((3 : ℝ) * (2 : ℝ) ^ (3 - 1) = 12) := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · intro r hr hrR
    unfold clusterToCoreRatio
    set C : ℝ := ((R - 1).factorial : ℝ) / (((r - 1).factorial : ℝ) * (2 : ℝ) ^ (R - 1))
    have hexp : (r : ℤ) - (R : ℤ) = -((R - r : ℕ) : ℤ) := by omega
    have hk_pos : 0 < R - r := by omega
    have hfn : (fun M : ℝ => C * M ^ ((r : ℤ) - (R : ℤ))) =
        fun M : ℝ => C * (M ^ (R - r))⁻¹ := by
      funext M; rw [hexp, zpow_neg, zpow_natCast]
    rw [hfn]
    have hpow : Tendsto (fun M : ℝ => M ^ (R - r)) atTop atTop :=
      tendsto_pow_atTop (Nat.pos_iff_ne_zero.mp hk_pos)
    have hinv : Tendsto (fun M : ℝ => (M ^ (R - r))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hpow
    simpa [mul_zero] using hinv.const_mul C
  · intro M hM
    unfold clusterToCoreRatio
    have hfac_ne : ((R - 1).factorial : ℝ) ≠ 0 := by positivity
    have hpow_ne : (2 : ℝ) ^ (R - 1) ≠ 0 := by positivity
    have heq : (((R - 1).factorial : ℝ) / (((R - 1).factorial : ℝ) * (2 : ℝ) ^ (R - 1))) *
        M ^ ((R : ℤ) - (R : ℤ)) = (2 : ℝ) ^ (-(R - 1 : ℤ)) := by
      rw [sub_self, zpow_zero, mul_one, zpow_neg]
      have hcast : ((R - 1 : ℤ)) = ((R - 1 : ℕ) : ℤ) := by omega
      rw [hcast, zpow_natCast]
      field_simp [hfac_ne, hpow_ne]
    refine ⟨heq, ?_⟩
    rw [heq, zpow_neg]
    have hcast : ((R - 1 : ℤ)) = ((R - 1 : ℕ) : ℤ) := by omega
    rw [hcast, zpow_natCast, one_div]
    refine inv_anti₀ (by norm_num : (0 : ℝ) < 2) ?_
    have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (R - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using h1
  · intro r hr
    unfold clusterToCoreRatio
    set C : ℝ := ((R - 1).factorial : ℝ) / (((r - 1).factorial : ℝ) * (2 : ℝ) ^ (R - 1))
    have hC_pos : 0 < C := by positivity
    have hexp : (r : ℤ) - (R : ℤ) = ((r - R : ℕ) : ℤ) := by omega
    have hk_pos : 0 < r - R := by omega
    have hfn : (fun M : ℝ => C * M ^ ((r : ℤ) - (R : ℤ))) =
        fun M : ℝ => C * M ^ (r - R) := by
      funext M; rw [hexp, zpow_natCast]
    rw [hfn]
    exact Tendsto.const_mul_atTop hC_pos (tendsto_pow_atTop (Nat.pos_iff_ne_zero.mp hk_pos))
  · intro M _
    unfold clusterToCoreRatio
    have h1 : ((R + 1 : ℕ) : ℤ) - (R : ℤ) = 1 := by omega
    rw [h1, zpow_one]
    have hsub : R + 1 - 1 = R := by omega
    rw [hsub]
    obtain ⟨k, rfl⟩ : ∃ k, R = k + 1 := ⟨R - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
    have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp [hk1, hkf, hp]

end SpectralEclipse
