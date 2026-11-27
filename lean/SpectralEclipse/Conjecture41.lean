/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Chains456
import Mathlib.Tactic

/-!
# Complete Machine-Checked Resolution of Conjecture 4.1 (Escobar-Garcia-Minenkova, arXiv:2507.18767v1)

Proves **Theorem 4 (`conjecture_4_1_7x7`)**: For ANY `7 × 7` persymmetric Jacobi matrix realizing
PST with centered symmetric spectrum `{0, ±λ₁, ±λ₂, ±λ₃}` (reduced to `0 < λ₁ < λ₂ < λ₃`,
`λ₁` odd, `λ₂` even, `λ₃` odd, `gcd(λ₁, λ₂, λ₃) = 1`), Early State Exclusion is absent if and
only if `λ₁` divides both `λ₂` and `λ₃` (equivalently `λ₁ = 1` in reduced form):
  - **Forward (`amp7_pos_of_x_eq_one`)**: Holds for ALL real `1 < y < z` (via `H_slope_strictAnti`
    from the positive-kernel Bernstein certificate `HDeriv2_pos` on `(0, 3.3]` + algebraic tail
    bound on `[3.3, ∞)`).
  - **Converse (`amp7_hasESE_of_x_ge_three`)**: Discrete Fourier Coset-Averaging Theorem over
    `t_m(s) = (2m + 1) π / λ₁ + s` (`m = 0, ..., λ₁ - 1`), covering all 3 divisibility cases:
      * Case 1 (`λ₁ ∤ λ₂`, `λ₁ ∤ λ₃`): `Ā(0) = c₃ - c₂ < 0`.
      * Case 2 (`λ₁ ∤ λ₂`, `λ₁ ∣ λ₃`): `Ā(0) = -c₂ < 0`.
      * Case 3 (`λ₁ ∣ λ₂`, `λ₁ ∤ λ₃`): Universal shift `s = 2 / λ₃` yields `Ā(2/λ₃) < -(1/9) c₃ < 0`!
  - **General Scaling Corollary (`conjecture_4_1_7x7_unreduced`)**: Restates Conjecture 4.1 verbatim
    for arbitrary unreduced positive eigenvalues `0 < α₁ < α₂ < α₃` with PST alternating parity,
    showing `¬HasESEReal_scaled ↔ α₁ ∣ α₂ ∧ α₁ ∣ α₃`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SpectralEclipse

/-! ### Part A: Forward Direction (`λ₁ = 1` implies NO ESE for ALL real `1 < y < z`) -/

/-- Exact divided-difference positivity for `7 × 7` symmetric PST chain when `λ₁ = 1`, `λ₂` even,
`λ₃` odd (in fact proved using only the parity of `λ₂` and `λ₃`, matching `H_slope_strictAnti`). -/
theorem amp7_pos_of_x_eq_one {y z : ℕ} (hy_even : Even y) (hz_odd : Odd z)
    (h1y : 1 < y) (hyz : y < z) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < Real.pi) :
    0 < amp7 1 (y : ℝ) (z : ℝ) t := by
  have hy_r : (1 : ℝ) < (y : ℝ) := by exact_mod_cast h1y
  have hz_r : (y : ℝ) < (z : ℝ) := by exact_mod_cast hyz
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
  have hy1 : (0 : ℝ) < (y : ℝ) ^ 2 - 1 := by nlinarith
  have hz1 : (0 : ℝ) < (z : ℝ) ^ 2 - 1 := by nlinarith
  have hzy : (0 : ℝ) < (z : ℝ) ^ 2 - (y : ℝ) ^ 2 := by nlinarith
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · unfold amp7
    simp only [mul_zero, Real.cos_zero, mul_one]
    have hden : 0 < 1 / (1 ^ 2 * (y : ℝ) ^ 2 * (z : ℝ) ^ 2) +
        1 / (1 ^ 2 * ((y : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - 1 ^ 2)) +
        1 / ((y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) +
        1 / ((z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) := by
      have : (1 : ℝ) ^ 2 = 1 := one_pow 2
      rw [this]; positivity
    rw [div_self hden.ne']
    norm_num
  · set u := (Real.pi - t) / 2
    have hu0 : 0 < u := by simp only [u]; linarith
    have hu : u < Real.pi / 2 := by simp only [u]; linarith
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu0
    have ht_eq : t = Real.pi - 2 * u := by simp only [u]; ring
    rw [ht_eq]
    unfold amp7
    have hden : 0 < 1 / (1 ^ 2 * (y : ℝ) ^ 2 * (z : ℝ) ^ 2) +
        1 / (1 ^ 2 * ((y : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - 1 ^ 2)) +
        1 / ((y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) +
        1 / ((z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) := by
      have : (1 : ℝ) ^ 2 = 1 := one_pow 2
      rw [this]; positivity
    refine div_pos ?_ hden
    have hc1 : Real.cos (1 * (Real.pi - 2 * u)) = -(1 - 2 * Real.sin u ^ 2) := by
      rw [one_mul, Real.cos_pi_sub, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq u
      linarith
    have hcy : Real.cos ((y : ℝ) * (Real.pi - 2 * u)) = 1 - 2 * Real.sin ((y : ℝ) * u) ^ 2 := by
      rcases hy_even with ⟨m, rfl⟩
      have harg : ((m + m : ℕ) : ℝ) * (Real.pi - 2 * u) =
          -(2 * (((m + m : ℕ) : ℝ) * u)) + (m : ℝ) * (2 * Real.pi) := by
        push_cast; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (((m + m : ℕ) : ℝ) * u)
      linarith
    have hcz : Real.cos ((z : ℝ) * (Real.pi - 2 * u)) = -(1 - 2 * Real.sin ((z : ℝ) * u) ^ 2) := by
      rcases hz_odd with ⟨m, rfl⟩
      have harg : ((2 * m + 1 : ℕ) : ℝ) * (Real.pi - 2 * u) =
          -(2 * (((2 * m + 1 : ℕ) : ℝ) * u)) + Real.pi + (m : ℝ) * (2 * Real.pi) := by
        push_cast; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, Real.cos_neg, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (((2 * m + 1 : ℕ) : ℝ) * u)
      linarith
    rw [hc1, hcy, hcz]
    have hH1 : Real.sin u ^ 2 = u ^ 2 * H (u ^ 2) := by
      rw [H_sq hu0]; field_simp [hu0.ne']
    have hHy : Real.sin ((y : ℝ) * u) ^ 2 = ((y : ℝ) * u) ^ 2 * H (((y : ℝ) * u) ^ 2) := by
      rw [H_sq (mul_pos hy0 hu0)]; field_simp [hy0.ne', hu0.ne']
    have hHz : Real.sin ((z : ℝ) * u) ^ 2 = ((z : ℝ) * u) ^ 2 * H (((z : ℝ) * u) ^ 2) := by
      rw [H_sq (mul_pos hz0 hu0)]; field_simp [hz0.ne', hu0.ne']
    rw [hH1, hHy, hHz]
    have hyu_lt : u ^ 2 < ((y : ℝ) * u) ^ 2 := by
      have : ((y : ℝ) * u) ^ 2 - u ^ 2 = ((y : ℝ) ^ 2 - 1) * u ^ 2 := by ring
      nlinarith [mul_pos hy1 hu2]
    have hyzu_lt : ((y : ℝ) * u) ^ 2 < ((z : ℝ) * u) ^ 2 := by
      have : ((z : ℝ) * u) ^ 2 - ((y : ℝ) * u) ^ 2 = ((z : ℝ) ^ 2 - (y : ℝ) ^ 2) * u ^ 2 := by ring
      nlinarith [mul_pos hzy hu2]
    have hslope := H_slope_strictAnti hu0 hu hyu_lt hyzu_lt
    have hid :
        1 / (1 ^ 2 * (y : ℝ) ^ 2 * (z : ℝ) ^ 2) +
        1 / (1 ^ 2 * ((y : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - 1 ^ 2)) *
          -(1 - 2 * (u ^ 2 * H (u ^ 2))) +
        1 / ((y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) *
          (1 - 2 * (((y : ℝ) * u) ^ 2 * H (((y : ℝ) * u) ^ 2))) +
        1 / ((z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - 1 ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) *
          -(1 - 2 * (((z : ℝ) * u) ^ 2 * H (((z : ℝ) * u) ^ 2))) =
        (2 * u ^ 4 / ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) *
          ((H (u ^ 2) - H (((y : ℝ) * u) ^ 2)) / (((y : ℝ) * u) ^ 2 - u ^ 2) -
           (H (u ^ 2) - H (((z : ℝ) * u) ^ 2)) / (((z : ℝ) * u) ^ 2 - u ^ 2)) := by
      have hyu_sub : ((y : ℝ) * u) ^ 2 - u ^ 2 ≠ 0 := (sub_pos.mpr hyu_lt).ne'
      have hzu_sub : ((z : ℝ) * u) ^ 2 - u ^ 2 ≠ 0 := (sub_pos.mpr (lt_trans hyu_lt hyzu_lt)).ne'
      field_simp [hy0.ne', hz0.ne', hy1.ne', hz1.ne', hzy.ne', hyu_sub, hzu_sub]
      ring
    rw [hid]
    exact mul_pos (div_pos (by positivity) hzy) (sub_pos.mpr hslope)

/-! ### Part B: Converse Direction via Discrete Fourier Coset-Averaging Theorem -/

/-- Exact discrete Fourier cosine orthogonality on the shifted odd-multiple coset
`t_m(s) = (2m + 1) π / x + s` (`m = 0, ..., x - 1`):
  * If `x ∣ k`, then `∑_{m=0}^{x-1} cos(k t_m(s)) = x * (-1)^(k/x) * cos(k s)`.
  * If `x ∤ k`, then `∑_{m=0}^{x-1} cos(k t_m(s)) = 0`. -/
theorem sum_cos_coset_dvd {x k : ℕ} (hx : 0 < x) (hdvd : x ∣ k) (s : ℝ) :
    ∑ m ∈ Finset.range x, Real.cos ((k : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s)) =
      (x : ℝ) * ((-1 : ℝ) ^ (k / x) * Real.cos ((k : ℝ) * s)) := by
  rcases hdvd with ⟨q, rfl⟩
  have hqx : x * q / x = q := Nat.mul_div_right q hx
  rw [hqx]
  have hx_ne : (x : ℝ) ≠ 0 := by positivity
  have hterm : ∀ m ∈ Finset.range x,
      Real.cos (((x * q : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s)) =
        (-1 : ℝ) ^ q * Real.cos (((x * q : ℕ) : ℝ) * s) := by
    intro m _
    have harg : ((x * q : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s) =
        ((x * q : ℕ) : ℝ) * s + (q : ℝ) * Real.pi + ((m * q : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; field_simp [hx_ne]; ring
    rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_pi]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_cos_coset_not_dvd {x k : ℕ} (hx : 0 < x) (hndvd : ¬(x ∣ k)) (s : ℝ) :
    ∑ m ∈ Finset.range x, Real.cos ((k : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s)) =
      0 := by
  have hx_ne : (x : ℝ) ≠ 0 := by positivity
  set α : ℝ := (k : ℝ) * Real.pi / (x : ℝ)
  have hsin_ne : Real.sin α ≠ 0 := by
    intro h0
    rw [Real.sin_eq_zero_iff] at h0
    rcases h0 with ⟨n, hn⟩
    have h1 : (n : ℝ) * (x : ℝ) = (k : ℝ) := by
      have : (n : ℝ) * Real.pi = (k : ℝ) * Real.pi / (x : ℝ) := hn
      have hmul := congrArg (· * (x : ℝ)) this
      field_simp [hx_ne] at hmul
      exact hmul
    have hn_nn : 0 ≤ n := by
      by_contra hlt
      push Not at hlt
      have : (n : ℝ) * (x : ℝ) < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hlt) (by positivity)
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    lift n to ℕ using hn_nn
    have hk_eq : k = x * n := by
      have hr : (k : ℝ) = ((x * n : ℕ) : ℝ) := by
        push_cast at h1 ⊢
        linarith
      exact_mod_cast hr
    exact hndvd ⟨n, hk_eq⟩
  -- Telescoping product-to-sum identity: `2 sin α * cos(θ + 2mα) = sin(θ + (2m+1)α) - sin(θ + (2m-1)α)`
  have hteles : 2 * Real.sin α *
      ∑ m ∈ Finset.range x, Real.cos ((k : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s)) =
      ∑ m ∈ Finset.range x,
        (Real.sin ((k : ℝ) * s + ((2 * (m + 1) : ℕ) : ℝ) * α) -
         Real.sin ((k : ℝ) * s + ((2 * m : ℕ) : ℝ) * α)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have harg : (k : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s) =
        (k : ℝ) * s + ((2 * m + 1 : ℕ) : ℝ) * α := by
      simp only [α]; push_cast; ring
    rw [harg]
    have hs1 := Real.sin_add ((k : ℝ) * s + ((2 * m + 1 : ℕ) : ℝ) * α) α
    have hs2 := Real.sin_sub ((k : ℝ) * s + ((2 * m + 1 : ℕ) : ℝ) * α) α
    have ha1 : (k : ℝ) * s + ((2 * m + 1 : ℕ) : ℝ) * α + α =
        (k : ℝ) * s + ((2 * (m + 1) : ℕ) : ℝ) * α := by push_cast; ring
    have ha2 : (k : ℝ) * s + ((2 * m + 1 : ℕ) : ℝ) * α - α =
        (k : ℝ) * s + ((2 * m : ℕ) : ℝ) * α := by push_cast; ring
    rw [ha1] at hs1
    rw [ha2] at hs2
    linarith
  rw [Finset.sum_range_sub (fun m => Real.sin ((k : ℝ) * s + ((2 * m : ℕ) : ℝ) * α)) x] at hteles
  have hend : Real.sin ((k : ℝ) * s + ((2 * x : ℕ) : ℝ) * α) = Real.sin ((k : ℝ) * s) := by
    have : (k : ℝ) * s + ((2 * x : ℕ) : ℝ) * α = (k : ℝ) * s + (k : ℝ) * (2 * Real.pi) := by
      simp only [α]; push_cast; field_simp [hx_ne]
    rw [this, Real.sin_add_nat_mul_two_pi]
  simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, add_zero, hend, sub_self] at hteles
  rcases mul_eq_zero.mp hteles with h2s | hsum
  · exact absurd (by linarith [mul_eq_zero.mp h2s] : Real.sin α = 0) hsin_ne
  · exact hsum

/-- Folding any real time `t` into `[0, π]` preserves `amp7 x y z` (since `cos(k t)` is even and
`2π`-periodic for integer `k`). -/
theorem amp7_fold_to_Icc (x y z : ℕ) (t : ℝ) :
    ∃ t' ∈ Set.Icc (0 : ℝ) Real.pi, amp7 (x : ℝ) (y : ℝ) (z : ℝ) t' = amp7 (x : ℝ) (y : ℝ) (z : ℝ) t := by
  let q : ℤ := ⌊t / (2 * Real.pi)⌋
  let r : ℝ := t - (q : ℝ) * (2 * Real.pi)
  have hr0 : 0 ≤ r := by
    have hq : (q : ℝ) ≤ t / (2 * Real.pi) := Int.floor_le (t / (2 * Real.pi))
    have h2pi : 0 < 2 * Real.pi := by positivity
    have := (le_div_iff₀ h2pi).mp hq
    linarith
  have hr2pi : r < 2 * Real.pi := by
    have hq : t / (2 * Real.pi) < (q : ℝ) + 1 := Int.lt_floor_add_one (t / (2 * Real.pi))
    have h2pi : 0 < 2 * Real.pi := by positivity
    have := (div_lt_iff₀ h2pi).mp hq
    linarith
  have hcos_shift : ∀ k : ℕ, Real.cos ((k : ℝ) * r) = Real.cos ((k : ℝ) * t) := by
    intro k
    have : (k : ℝ) * t = (k : ℝ) * r + ((k * q : ℤ) : ℝ) * (2 * Real.pi) := by
      simp only [r]; push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  by_cases hrpi : r ≤ Real.pi
  · refine ⟨r, ⟨hr0, hrpi⟩, ?_⟩
    unfold amp7
    rw [hcos_shift x, hcos_shift y, hcos_shift z]
  · push Not at hrpi
    refine ⟨2 * Real.pi - r, ⟨by linarith, by linarith⟩, ?_⟩
    have hcos_refl : ∀ k : ℕ, Real.cos ((k : ℝ) * (2 * Real.pi - r)) = Real.cos ((k : ℝ) * t) := by
      intro k
      have : (k : ℝ) * (2 * Real.pi - r) = -((k : ℝ) * r) + (k : ℝ) * (2 * Real.pi) := by ring
      rw [this, Real.cos_add_nat_mul_two_pi, Real.cos_neg, hcos_shift k]
    unfold amp7
    rw [hcos_refl x, hcos_refl y, hcos_refl z]

/-- Exact vanishing of `amp7` at `t = π` whenever `x, z` are odd and `y` is even. -/
theorem amp7_pi_eq_zero {x y z : ℕ} (hx_odd : Odd x) (hy_even : Even y) (hz_odd : Odd z)
    (hxy : x < y) (hyz : y < z) :
    amp7 (x : ℝ) (y : ℝ) (z : ℝ) Real.pi = 0 := by
  have hx0 : 0 < x := by rcases hx_odd with ⟨m, rfl⟩; omega
  have hx_r : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hy_r : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hz_r : (y : ℝ) < (z : ℝ) := by exact_mod_cast hyz
  have hyx : (0 : ℝ) < (y : ℝ) ^ 2 - (x : ℝ) ^ 2 := by nlinarith
  have hzx : (0 : ℝ) < (z : ℝ) ^ 2 - (x : ℝ) ^ 2 := by nlinarith
  have hzy : (0 : ℝ) < (z : ℝ) ^ 2 - (y : ℝ) ^ 2 := by nlinarith
  have hcx : Real.cos ((x : ℝ) * Real.pi) = -1 := by
    rcases hx_odd with ⟨m, rfl⟩
    rw [Real.cos_nat_mul_pi]
    simp [pow_add, pow_mul]
  have hcy : Real.cos ((y : ℝ) * Real.pi) = 1 := by
    rcases hy_even with ⟨m, rfl⟩
    rw [Real.cos_nat_mul_pi]
    have : m + m = 2 * m := by omega
    rw [this, pow_mul]
    norm_num
  have hcz : Real.cos ((z : ℝ) * Real.pi) = -1 := by
    rcases hz_odd with ⟨m, rfl⟩
    rw [Real.cos_nat_mul_pi]
    simp [pow_add, pow_mul]
  unfold amp7
  dsimp only
  rw [hcx, hcy, hcz]
  have hnum : 1 / ((x : ℝ) ^ 2 * (y : ℝ) ^ 2 * (z : ℝ) ^ 2) +
      1 / ((x : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2)) * (-1) +
      1 / ((y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) * 1 +
      1 / ((z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) * (-1) = 0 := by
    field_simp [hx_r.ne', (show (0 : ℝ) < (y : ℝ) by linarith).ne',
      (show (0 : ℝ) < (z : ℝ) by linarith).ne', hyx.ne', hzx.ne', hzy.ne']
    ring
  rw [hnum, zero_div]

/-- If the coset sum `∑_{m=0}^{x-1} amp7 x y z ((2m+1)π/x + s) < 0` for some real `s`,
then `amp7 x y z` has Early State Exclusion (`HasESEReal`). -/
theorem amp7_hasESE_of_coset_sum_neg {x y z : ℕ} (hx_odd : Odd x) (hy_even : Even y)
    (hz_odd : Odd z) (hxy : x < y) (hyz : y < z) {s : ℝ}
    (hsum_neg : ∑ m ∈ Finset.range x,
      amp7 (x : ℝ) (y : ℝ) (z : ℝ) (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s) < 0) :
    HasESEReal (amp7 (x : ℝ) (y : ℝ) (z : ℝ)) := by
  have hx0 : 0 < x := by rcases hx_odd with ⟨m, rfl⟩; omega
  have hx_r : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hy_r : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hz_r : (y : ℝ) < (z : ℝ) := by exact_mod_cast hyz
  have hyx : (0 : ℝ) < (y : ℝ) ^ 2 - (x : ℝ) ^ 2 := by nlinarith
  have hzx : (0 : ℝ) < (z : ℝ) ^ 2 - (x : ℝ) ^ 2 := by nlinarith
  have hzy : (0 : ℝ) < (z : ℝ) ^ 2 - (y : ℝ) ^ 2 := by nlinarith
  have hex : ∃ m ∈ Finset.range x,
      amp7 (x : ℝ) (y : ℝ) (z : ℝ) (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s) < 0 := by
    by_contra hall
    push Not at hall
    have hnn := Finset.sum_nonneg hall
    linarith
  rcases hex with ⟨m, _, hm_neg⟩
  rcases amp7_fold_to_Icc x y z (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s) with
    ⟨t0, ⟨ht0_ge, ht0_le⟩, ht0_eq⟩
  have hA0 : amp7 (x : ℝ) (y : ℝ) (z : ℝ) 0 = 1 := by
    unfold amp7
    simp only [mul_zero, Real.cos_zero, mul_one]
    have hden : 0 < 1 / ((x : ℝ) ^ 2 * (y : ℝ) ^ 2 * (z : ℝ) ^ 2) +
        1 / ((x : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2)) +
        1 / ((y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) +
        1 / ((z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2)) := by
      have : (0 : ℝ) < (y : ℝ) := by linarith
      have : (0 : ℝ) < (z : ℝ) := by linarith
      positivity
    exact div_self hden.ne'
  have hApi : amp7 (x : ℝ) (y : ℝ) (z : ℝ) Real.pi = 0 :=
    amp7_pi_eq_zero hx_odd hy_even hz_odd hxy hyz
  have ht0_pos : 0 < t0 := by
    rcases eq_or_lt_of_le ht0_ge with rfl | hpos
    · linarith
    · exact hpos
  have ht0_lt : t0 < Real.pi := by
    rcases eq_or_lt_of_le ht0_le with rfl | hlt
    · linarith
    · exact hlt
  have hcont : Continuous (amp7 (x : ℝ) (y : ℝ) (z : ℝ)) := by unfold amp7; fun_prop
  exact hasESEReal_of_pos_zero_neg_pt hcont (by linarith) ht0_pos ht0_lt (by linarith)

/-- Converse of Conjecture 4.1 (`7 × 7`): If `x ≥ 3` is odd, `y` even, `z` odd, `x < y < z`,
and `¬(x ∣ y ∧ x ∣ z)` (in particular whenever `gcd(x, y, z) = 1` and `x ≥ 3`), then
`amp7 x y z` ALWAYS has Early State Exclusion! -/
theorem amp7_hasESE_of_not_dvd {x y z : ℕ} (hx_odd : Odd x) (hy_even : Even y) (hz_odd : Odd z)
    (hxy : x < y) (hyz : y < z) (hndvd : ¬(x ∣ y ∧ x ∣ z)) :
    HasESEReal (amp7 (x : ℝ) (y : ℝ) (z : ℝ)) := by
  have hx0 : 0 < x := by rcases hx_odd with ⟨m, rfl⟩; omega
  have hx_r : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hy_r : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hz_r : (y : ℝ) < (z : ℝ) := by exact_mod_cast hyz
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
  have hyx : (0 : ℝ) < (y : ℝ) ^ 2 - (x : ℝ) ^ 2 := by nlinarith
  have hzx : (0 : ℝ) < (z : ℝ) ^ 2 - (x : ℝ) ^ 2 := by nlinarith
  have hzy : (0 : ℝ) < (z : ℝ) ^ 2 - (y : ℝ) ^ 2 := by nlinarith
  set w0 : ℝ := 1 / ((x : ℝ) ^ 2 * (y : ℝ) ^ 2 * (z : ℝ) ^ 2)
  set w1 : ℝ := 1 / ((x : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2))
  set w2 : ℝ := 1 / ((y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2))
  set w3 : ℝ := 1 / ((z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2) * ((z : ℝ) ^ 2 - (y : ℝ) ^ 2))
  have hw0 : 0 < w0 := by positivity
  have hw1 : 0 < w1 := by positivity
  have hw2 : 0 < w2 := by positivity
  have hw3 : 0 < w3 := by positivity
  have hden : 0 < w0 + w1 + w2 + w3 := by linarith
  -- Key exact algebraic identities among Hochstadt weights:
  have hid_alt : w0 - w1 + w2 - w3 = 0 := by
    simp only [w0, w1, w2, w3]
    field_simp [hx_r.ne', hy0.ne', hz0.ne', hyx.ne', hzx.ne', hzy.ne']
    ring
  have hw3_lt_w2 : w3 < w2 := by
    simp only [w2, w3]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : (y : ℝ) ^ 2 * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) <
        (z : ℝ) ^ 2 * ((z : ℝ) ^ 2 - (x : ℝ) ^ 2) := by nlinarith
    nlinarith
  -- Helper expanding the coset sum of `amp7` at any shift `s`
  have hsum_expand : ∀ s : ℝ,
      ∑ m ∈ Finset.range x,
        amp7 (x : ℝ) (y : ℝ) (z : ℝ) (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s) =
      ((x : ℝ) * w0 +
        w1 * ∑ m ∈ Finset.range x, Real.cos ((x : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s)) +
        w2 * ∑ m ∈ Finset.range x, Real.cos ((y : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s)) +
        w3 * ∑ m ∈ Finset.range x, Real.cos ((z : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * Real.pi / (x : ℝ) + s))) /
        (w0 + w1 + w2 + w3) := by
    intro s
    unfold amp7
    dsimp only
    rw [← Finset.sum_div]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, w0, w1, w2, w3]
  by_cases hxy_dvd : x ∣ y
  · -- Case 3: `x ∣ y` and `x ∤ z` — evaluate at the universal point `s = 2 / z`!
    have hxz_ndvd : ¬(x ∣ z) := fun h => hndvd ⟨hxy_dvd, h⟩
    have hy_div_even : Even (y / x) := by
      rcases hxy_dvd with ⟨q, hq⟩
      have hqx : y / x = q := by rw [hq]; exact Nat.mul_div_right q hx0
      rw [hqx]
      rcases hx_odd with ⟨a, ha⟩
      rcases hy_even with ⟨b, hb⟩
      have hmod := congrArg (· % 2) hq
      rw [Nat.mul_mod, show x % 2 = 1 by omega, show y % 2 = 0 by omega] at hmod
      have hq_even : q % 2 = 0 := by omega
      exact ⟨q / 2, by omega⟩
    have hy_ge_2x : 2 * x ≤ y := by
      rcases hxy_dvd with ⟨q, hq⟩
      have hq_gt1 : 1 < q := by nlinarith
      nlinarith
    set s : ℝ := 2 / (z : ℝ)
    refine amp7_hasESE_of_coset_sum_neg hx_odd hy_even hz_odd hxy hyz (s := s) ?_
    rw [hsum_expand s]
    refine div_neg_of_neg_of_pos ?_ hden
    have hSx := sum_cos_coset_dvd hx0 (dvd_refl x) s
    rw [Nat.div_self hx0, pow_one] at hSx
    have hSy := sum_cos_coset_dvd hx0 hxy_dvd s
    have hsign_y : (-1 : ℝ) ^ (y / x) = 1 := by
      rcases hy_div_even with ⟨k, hk⟩
      rw [hk, show k + k = 2 * k by omega, pow_mul]
      norm_num
    rw [hsign_y, one_mul] at hSy
    have hSz := sum_cos_coset_not_dvd hx0 hxz_ndvd s
    rw [hSx, hSy, hSz, mul_zero, add_zero]
    -- Numerator = `x * (w0 - w1 * cos(x s) + w2 * cos(y s))`
    --           = `x * (w3 + w1 * (1 - cos(x s)) - w2 * (1 - cos(y s)))`!
    have hnum_eq : (x : ℝ) * w0 + w1 * ((x : ℝ) * (-1 * Real.cos ((x : ℝ) * s))) +
        w2 * ((x : ℝ) * Real.cos ((y : ℝ) * s)) =
        (x : ℝ) * (w3 + w1 * (1 - Real.cos ((x : ℝ) * s)) - w2 * (1 - Real.cos ((y : ℝ) * s))) := by
      have hw0_eq : w0 = w1 - w2 + w3 := by linarith [hid_alt]
      rw [hw0_eq]; ring
    rw [hnum_eq]
    refine mul_neg_of_pos_of_neg hx_r ?_
    -- Exact algebraic moment identity: `x² w1 - y² w2 = -z² w3`!
    have hmoment : (x : ℝ) ^ 2 * w1 - (y : ℝ) ^ 2 * w2 = -(z : ℝ) ^ 2 * w3 := by
      simp only [w1, w2, w3]
      field_simp [hx_r.ne', hy0.ne', hz0.ne', hyx.ne', hzx.ne', hzy.ne']
      ring
    -- Apply `1 - cos(x s) ≤ (x s)² / 2` and `1 - cos(y s) ≥ (y s)² / 2 - (y s)⁴ / 24`!
    have hb1 := one_sub_cos_le_sq_div_two ((x : ℝ) * s)
    have hb2 := sq_div_two_sub_pow4_div_24_le_one_sub_cos ((y : ℝ) * s)
    -- Bound `(y s)⁴ / 24 * w2 < (8/9) * w3` using `s = 2/z`, `y ≥ 2x`, and `y < z`!
    have hys4 : w2 * (((y : ℝ) * s) ^ 4 / 24) < (8 / 9 : ℝ) * w3 := by
      have hs_eq : (y : ℝ) * s = 2 * (y : ℝ) / (z : ℝ) := by simp only [s]; ring
      rw [hs_eq]
      have hy_ge2 : 2 * (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy_ge_2x
      have hrat1 : (y : ℝ) ^ 2 ≤ (4 / 3 : ℝ) * ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) := by nlinarith
      have hrat2 : (z : ℝ) ^ 2 - (x : ℝ) ^ 2 < (z : ℝ) ^ 2 := by nlinarith
      have hw2_ratio : w2 * (y : ℝ) ^ 4 / (z : ℝ) ^ 4 =
          w3 * ((y : ℝ) ^ 2 / ((y : ℝ) ^ 2 - (x : ℝ) ^ 2)) *
            (((z : ℝ) ^ 2 - (x : ℝ) ^ 2) / (z : ℝ) ^ 2) := by
        simp only [w2, w3]
        field_simp [hy0.ne', hz0.ne', hyx.ne', hzx.ne', hzy.ne']
      have hcalc : w2 * ((2 * (y : ℝ) / (z : ℝ)) ^ 4 / 24) =
          (2 / 3 : ℝ) * (w2 * (y : ℝ) ^ 4 / (z : ℝ) ^ 4) := by ring
      rw [hcalc, hw2_ratio]
      have hf1 : (y : ℝ) ^ 2 / ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) ≤ 4 / 3 :=
        (div_le_iff₀ hyx).mpr hrat1
      have hf2 : ((z : ℝ) ^ 2 - (x : ℝ) ^ 2) / (z : ℝ) ^ 2 < 1 :=
        (div_lt_one (sq_pos_of_pos hz0)).mpr hrat2
      have hf1_pos : 0 < (y : ℝ) ^ 2 / ((y : ℝ) ^ 2 - (x : ℝ) ^ 2) := div_pos (sq_pos_of_pos hy0) hyx
      have hstep1 : w3 * ((y : ℝ) ^ 2 / ((y : ℝ) ^ 2 - (x : ℝ) ^ 2)) *
          (((z : ℝ) ^ 2 - (x : ℝ) ^ 2) / (z : ℝ) ^ 2) <
          w3 * ((y : ℝ) ^ 2 / ((y : ℝ) ^ 2 - (x : ℝ) ^ 2)) * 1 :=
        mul_lt_mul_of_pos_left hf2 (mul_pos hw3 hf1_pos)
      have hstep2 : w3 * ((y : ℝ) ^ 2 / ((y : ℝ) ^ 2 - (x : ℝ) ^ 2)) ≤ w3 * (4 / 3) :=
        mul_le_mul_of_nonneg_left hf1 hw3.le
      linarith
    have hquad : w1 * (((x : ℝ) * s) ^ 2 / 2) - w2 * (((y : ℝ) * s) ^ 2 / 2) = -2 * w3 := by
      have h1 : w1 * (((x : ℝ) * s) ^ 2 / 2) - w2 * (((y : ℝ) * s) ^ 2 / 2) =
          (s ^ 2 / 2) * ((x : ℝ) ^ 2 * w1 - (y : ℝ) ^ 2 * w2) := by ring
      rw [h1, hmoment]
      simp only [s]
      field_simp [hz0.ne']
    -- Final bound: `w3 + w1*(1-cos xs) - w2*(1-cos ys) < w3 - 2*w3 + (8/9)*w3 = -(1/9)*w3 < 0`!!
    have hmul1 : w1 * (1 - Real.cos ((x : ℝ) * s)) ≤ w1 * (((x : ℝ) * s) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hb1 hw1.le
    have hmul2 : w2 * (((y : ℝ) * s) ^ 2 / 2 - ((y : ℝ) * s) ^ 4 / 24) ≤
        w2 * (1 - Real.cos ((y : ℝ) * s)) :=
      mul_le_mul_of_nonneg_left hb2 hw2.le
    have hmul2' : w2 * (((y : ℝ) * s) ^ 2 / 2) - w2 * (((y : ℝ) * s) ^ 4 / 24) ≤
        w2 * (1 - Real.cos ((y : ℝ) * s)) := by linarith
    linarith
  · -- Cases 1 & 2 (`x ∤ y`): evaluate at `s = 0`!
    refine amp7_hasESE_of_coset_sum_neg hx_odd hy_even hz_odd hxy hyz (s := 0) ?_
    rw [hsum_expand 0]
    refine div_neg_of_neg_of_pos ?_ hden
    have hSx := sum_cos_coset_dvd hx0 (dvd_refl x) 0
    rw [Nat.div_self hx0, pow_one, mul_zero, Real.cos_zero, mul_one] at hSx
    have hSy := sum_cos_coset_not_dvd hx0 hxy_dvd 0
    rw [hSx, hSy, mul_zero, add_zero]
    by_cases hxz_dvd : x ∣ z
    · -- Case 2: `x ∤ y`, `x ∣ z` (`z/x` is odd since `z` is odd): `Ā(0) = -w2 < 0`!
      have hz_div_odd : Odd (z / x) := by
        rcases hxz_dvd with ⟨q, hq⟩
        have hqx : z / x = q := by rw [hq]; exact Nat.mul_div_right q hx0
        rw [hqx]
        rcases hx_odd with ⟨a, ha⟩
        rcases hz_odd with ⟨b, hb⟩
        have hmod := congrArg (· % 2) hq
        rw [Nat.mul_mod, show x % 2 = 1 by omega, show z % 2 = 1 by omega] at hmod
        have hq_odd : q % 2 = 1 := by omega
        exact ⟨q / 2, by omega⟩
      have hSz := sum_cos_coset_dvd hx0 hxz_dvd 0
      rw [mul_zero, Real.cos_zero, mul_one] at hSz
      have hsign_z : (-1 : ℝ) ^ (z / x) = -1 := by
        rcases hz_div_odd with ⟨k, hk⟩
        rw [hk, pow_add, pow_mul]
        norm_num
      rw [hsign_z] at hSz
      rw [hSz]
      have hnum_eq : (x : ℝ) * w0 + w1 * ((x : ℝ) * -1) + w3 * ((x : ℝ) * -1) = (x : ℝ) * (-w2) := by
        have hw0_eq : w0 = w1 - w2 + w3 := by linarith [hid_alt]
        rw [hw0_eq]; ring
      rw [hnum_eq]
      exact mul_neg_of_pos_of_neg hx_r (neg_neg_of_pos hw2)
    · -- Case 1: `x ∤ y`, `x ∤ z`: `Ā(0) = w3 - w2 < 0`!
      have hSz := sum_cos_coset_not_dvd hx0 hxz_dvd 0
      rw [hSz, mul_zero, add_zero]
      have hnum_eq : (x : ℝ) * w0 + w1 * ((x : ℝ) * -1) = (x : ℝ) * (w3 - w2) := by
        have hw0_eq : w0 = w1 - w2 + w3 := by linarith [hid_alt]
        rw [hw0_eq]; ring
      rw [hnum_eq]
      exact mul_neg_of_pos_of_neg hx_r (sub_neg.mpr hw3_lt_w2)

/-! ### Part C: Main Theorem 4 — Complete Resolution of Conjecture 4.1 (`7 × 7`) -/

/-- Exact time-scaling invariance of `amp7`: scaling all eigenvalues by `c > 0` scales time by `c`. -/
theorem amp7_scale {c x y z : ℝ} (hc : 0 < c) (t : ℝ) :
    amp7 (c * x) (c * y) (c * z) t = amp7 x y z (c * t) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  have hc6 : c ^ 6 ≠ 0 := pow_ne_zero 6 hc.ne'
  unfold amp7
  have h1 : (c * x) ^ 2 * (c * y) ^ 2 * (c * z) ^ 2 = c ^ 6 * (x ^ 2 * y ^ 2 * z ^ 2) := by ring
  have h2 : (c * x) ^ 2 * ((c * y) ^ 2 - (c * x) ^ 2) * ((c * z) ^ 2 - (c * x) ^ 2) =
      c ^ 6 * (x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2)) := by ring
  have h3 : (c * y) ^ 2 * ((c * y) ^ 2 - (c * x) ^ 2) * ((c * z) ^ 2 - (c * y) ^ 2) =
      c ^ 6 * (y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by ring
  have h4 : (c * z) ^ 2 * ((c * z) ^ 2 - (c * x) ^ 2) * ((c * z) ^ 2 - (c * y) ^ 2) =
      c ^ 6 * (z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)) := by ring
  rw [h1, h2, h3, h4]
  have ha1 : c * x * t = x * (c * t) := by ring
  have ha2 : c * y * t = y * (c * t) := by ring
  have ha3 : c * z * t = z * (c * t) := by ring
  rw [ha1, ha2, ha3]
  set A := x ^ 2 * y ^ 2 * z ^ 2
  set B := x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2)
  set C := y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)
  set D := z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2)
  have hdiv : ∀ u : ℝ, 1 / (c ^ 6 * u) = (1 / c ^ 6) * (1 / u) := fun u => by ring
  simp_rw [hdiv]
  have hnum : (1 / c ^ 6) * (1 / A) + (1 / c ^ 6) * (1 / B) * Real.cos (x * (c * t)) +
      (1 / c ^ 6) * (1 / C) * Real.cos (y * (c * t)) +
      (1 / c ^ 6) * (1 / D) * Real.cos (z * (c * t)) =
      (1 / c ^ 6) * (1 / A + 1 / B * Real.cos (x * (c * t)) +
        1 / C * Real.cos (y * (c * t)) + 1 / D * Real.cos (z * (c * t))) := by ring
  have hden : (1 / c ^ 6) * (1 / A) + (1 / c ^ 6) * (1 / B) +
      (1 / c ^ 6) * (1 / C) + (1 / c ^ 6) * (1 / D) =
      (1 / c ^ 6) * (1 / A + 1 / B + 1 / C + 1 / D) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (by positivity : (1 / c ^ 6 : ℝ) ≠ 0)]

/-- **Theorem 4 (Complete Resolution of Conjecture 4.1 of Escobar-Garcia-Minenkova, arXiv:2507.18767v1)**:
For any reduced `7 × 7` symmetric PST spectrum `{0, ±x, ±y, ±z}` (`x` odd, `y` even, `z` odd,
`x < y < z`, `gcd(x, gcd(y, z)) = 1`), the chain avoids Early State Exclusion on `(0, π)`
if and only if `x` divides both `y` and `z` (equivalently `x = 1`). -/
theorem conjecture_4_1_7x7 {x y z : ℕ} (hx_odd : Odd x) (hy_even : Even y) (hz_odd : Odd z)
    (hxy : x < y) (hyz : y < z) (hcop : Nat.gcd x (Nat.gcd y z) = 1) :
    ¬HasESEReal (amp7 (x : ℝ) (y : ℝ) (z : ℝ)) ↔ (x ∣ y ∧ x ∣ z) := by
  constructor
  · intro hno
    by_contra hndvd
    exact hno (amp7_hasESE_of_not_dvd hx_odd hy_even hz_odd hxy hyz hndvd)
  · rintro ⟨hxy_dvd, hxz_dvd⟩
    have hx_dvd_gcd : x ∣ Nat.gcd y z := Nat.dvd_gcd hxy_dvd hxz_dvd
    have hx_dvd_all : x ∣ Nat.gcd x (Nat.gcd y z) := Nat.dvd_gcd (dvd_refl x) hx_dvd_gcd
    rw [hcop] at hx_dvd_all
    have hx1 : x = 1 := Nat.dvd_one.mp hx_dvd_all
    subst hx1
    rintro ⟨τ, hτ0, hτpi, hzero⟩
    have hpos := amp7_pos_of_x_eq_one hy_even hz_odd hxy hyz hτ0.le hτpi
    simp only [Nat.cast_one] at hzero
    linarith

/-- **Unreduced Real-Scaled Conjecture 4.1 (`7 × 7`)**: For ANY positive real scale `c > 0`
and arbitrary positive eigenvalues `α = c * x < β = c * y < γ = c * z` with `x` odd, `y` even,
`z` odd and `g = gcd(x, gcd(y, z))` (so the minimum PST time is `T₀ = π / (c * g)`),
the `7 × 7` symmetric PST chain has NO Early State Exclusion before `T₀` if and only if
`x ∣ y ∧ x ∣ z` (equivalently `β / α ∈ ℤ` and `γ / α ∈ ℤ`). -/
theorem conjecture_4_1_7x7_unreduced {c : ℝ} (hc : 0 < c) {x y z : ℕ}
    (hx_odd : Odd x) (hy_even : Even y) (hz_odd : Odd z) (hxy : x < y) (hyz : y < z) :
    (∀ τ : ℝ, 0 < τ → τ < Real.pi / (c * (Nat.gcd x (Nat.gcd y z) : ℝ)) →
      amp7 (c * (x : ℝ)) (c * (y : ℝ)) (c * (z : ℝ)) τ ≠ 0) ↔
    (x ∣ y ∧ x ∣ z) := by
  set g := Nat.gcd x (Nat.gcd y z)
  have hx0 : 0 < x := by rcases hx_odd with ⟨m, rfl⟩; omega
  have hg_dvd_x : g ∣ x := Nat.gcd_dvd_left x (Nat.gcd y z)
  have hg_dvd_y : g ∣ y := dvd_trans (Nat.gcd_dvd_right x (Nat.gcd y z)) (Nat.gcd_dvd_left y z)
  have hg_dvd_z : g ∣ z := dvd_trans (Nat.gcd_dvd_right x (Nat.gcd y z)) (Nat.gcd_dvd_right y z)
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg_dvd_x hx0
  have hg_r : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  set x' := x / g
  set y' := y / g
  set z' := z / g
  have hx_eq : x = g * x' := (Nat.mul_div_cancel' hg_dvd_x).symm
  have hy_eq : y = g * y' := (Nat.mul_div_cancel' hg_dvd_y).symm
  have hz_eq : z = g * z' := (Nat.mul_div_cancel' hg_dvd_z).symm
  have hg_odd : Odd g := by
    rcases hx_odd with ⟨a, ha⟩
    have : g % 2 = 1 := by
      by_contra he
      have h2g : 2 ∣ g := by omega
      have h2x : 2 ∣ x := dvd_trans h2g hg_dvd_x
      omega
    exact ⟨g / 2, by omega⟩
  have hx'_odd : Odd x' := by
    rcases hx_odd with ⟨a, ha⟩
    rcases hg_odd with ⟨b, hb⟩
    have : x' % 2 = 1 := by
      by_contra he
      have h2 : 2 ∣ x' := by omega
      have h2x : 2 ∣ x := by rw [hx_eq]; exact dvd_mul_of_dvd_right h2 g
      omega
    exact ⟨x' / 2, by omega⟩
  have hy'_even : Even y' := by
    rcases hy_even with ⟨a, ha⟩
    rcases hg_odd with ⟨b, hb⟩
    have : y' % 2 = 0 := by
      by_contra ho
      have h1 : y' % 2 = 1 := by omega
      have hgy_odd : (g * y') % 2 = 1 := by
        rw [Nat.mul_mod, show g % 2 = 1 by omega, h1]
      omega
    exact ⟨y' / 2, by omega⟩
  have hz'_odd : Odd z' := by
    rcases hz_odd with ⟨a, ha⟩
    rcases hg_odd with ⟨b, hb⟩
    have : z' % 2 = 1 := by
      by_contra he
      have h2 : 2 ∣ z' := by omega
      have h2z : 2 ∣ z := by rw [hz_eq]; exact dvd_mul_of_dvd_right h2 g
      omega
    exact ⟨z' / 2, by omega⟩
  have hx'y' : x' < y' := by nlinarith [hx_eq, hy_eq]
  have hy'z' : y' < z' := by nlinarith [hy_eq, hz_eq]
  have hcop' : Nat.gcd x' (Nat.gcd y' z') = 1 := by
    have hmul : g * Nat.gcd x' (Nat.gcd y' z') = g := by
      calc g * Nat.gcd x' (Nat.gcd y' z')
          = Nat.gcd (g * x') (g * Nat.gcd y' z') := (Nat.gcd_mul_left g x' (Nat.gcd y' z')).symm
        _ = Nat.gcd (g * x') (Nat.gcd (g * y') (g * z')) := by rw [Nat.gcd_mul_left g y' z']
        _ = Nat.gcd x (Nat.gcd y z) := by rw [← hx_eq, ← hy_eq, ← hz_eq]
        _ = g := rfl
    exact mul_left_cancel₀ hg0.ne' (hmul.trans (mul_one g).symm)
  have hamp_eq : ∀ τ : ℝ,
      amp7 (c * (x : ℝ)) (c * (y : ℝ)) (c * (z : ℝ)) τ =
        amp7 (x' : ℝ) (y' : ℝ) (z' : ℝ) ((c * (g : ℝ)) * τ) := by
    intro τ
    have h1 : c * (x : ℝ) = (c * (g : ℝ)) * (x' : ℝ) := by
      rw [hx_eq]; push_cast; ring
    have h2 : c * (y : ℝ) = (c * (g : ℝ)) * (y' : ℝ) := by
      rw [hy_eq]; push_cast; ring
    have h3 : c * (z : ℝ) = (c * (g : ℝ)) * (z' : ℝ) := by
      rw [hz_eq]; push_cast; ring
    rw [h1, h2, h3, amp7_scale (mul_pos hc hg_r)]
  have hdvd_iff : (x' ∣ y' ∧ x' ∣ z') ↔ (x ∣ y ∧ x ∣ z) := by
    rw [hx_eq, hy_eq, hz_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_dvd_mul_left g h1, mul_dvd_mul_left g h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Nat.mul_dvd_mul_iff_left hg0).mp h1, (Nat.mul_dvd_mul_iff_left hg0).mp h2⟩
  rw [← hdvd_iff, ← conjecture_4_1_7x7 hx'_odd hy'_even hz'_odd hx'y' hy'z' hcop']
  constructor
  · intro hno ⟨u, hu0, hupi, huzero⟩
    set τ := u / (c * (g : ℝ))
    have hcg : 0 < c * (g : ℝ) := mul_pos hc hg_r
    have hτ0 : 0 < τ := div_pos hu0 hcg
    have hτlt : τ < Real.pi / (c * (g : ℝ)) := div_lt_div_of_pos_right hupi hcg
    have hzero : amp7 (c * (x : ℝ)) (c * (y : ℝ)) (c * (z : ℝ)) τ = 0 := by
      rw [hamp_eq τ]
      have : c * (g : ℝ) * τ = u := mul_div_cancel₀ u hcg.ne'
      rw [this, huzero]
    exact hno τ hτ0 hτlt hzero
  · intro hno τ hτ0 hτlt hzero
    rw [hamp_eq τ] at hzero
    have hcg : 0 < c * (g : ℝ) := mul_pos hc hg_r
    have hu0 : 0 < c * (g : ℝ) * τ := mul_pos hcg hτ0
    have hupi : c * (g : ℝ) * τ < Real.pi := by
      have := (lt_div_iff₀ hcg).mp hτlt
      linarith
    exact hno ⟨c * (g : ℝ) * τ, hu0, hupi, hzero⟩

end SpectralEclipse
