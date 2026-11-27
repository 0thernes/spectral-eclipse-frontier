/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.TrigBounds
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Complete Dichotomies for `4 × 4`, `5 × 5`, `6 × 6`, and Universal Even-Chain Orthogonality

Proves Theorems 1, 2, and 3 of the linked ESE chain:
  - **Universal Even-Chain Converse (`even_hasESE_of_min_ge_three`)**: For EVERY even length
    `2n ≥ 2` with odd positive integer spectrum `3 ≤ p_0 < p_1 < ... < p_{n-1}`, orthogonality
    against `cos(t/2)` on `[0, π]` forces an interior sign change, hence ESE!
  - **Theorem 1 (`dichotomy_4x4`)**: For reduced `4 × 4` symmetric PST spectra `{±p/2, ±q/2}`
    (`p < q` odd, `q - p ≡ 2 (mod 4)`, `gcd(p, q) = 1`), `¬HasESEReal (amp4 p q) ↔ p = 1`
    (equivalently `p ∣ q`).
  - **Theorem 2 (`dichotomy_5x5`)**: Machine-checked proof of the Enriquez-Minenkova (2026)
    `5 × 5` dichotomy: for `{0, ±y, ±x}` (`y` odd, `x` even, `0 < y < x`, `gcd(y, x) = 1`),
    `¬HasESEReal (amp5 y x) ↔ y = 1` (equivalently `y ∣ x`).
  - **Theorem 3 (`dichotomy_6x6`)**: Complete resolution of the `6 × 6` critical even dichotomy:
    for `{±p/2, ±q/2, ±r/2}` (`p < q < r` odd, alternating mod 4, `gcd(p, q, r) = 1`),
    `¬HasESEReal (amp6 p q r) ↔ p = 1` (equivalently `p ∣ q ∧ p ∣ r`).
-/

@[expose] public section

open scoped BigOperators
open Finset intervalIntegral

namespace SpectralEclipse

/-! ### Helper: Intermediate Value Theorem Wrapper for ESE -/

/-- If a continuous real amplitude satisfies `A(0) > 0` and `A(t₀) < 0` for some `t₀ ∈ (0, π)`,
then it has Early State Exclusion (`∃ τ ∈ (0, π), A τ = 0`). -/
theorem hasESEReal_of_pos_zero_neg_pt {A : ℝ → ℝ} (hcont : Continuous A)
    (h0 : 0 < A 0) {t0 : ℝ} (ht0_pos : 0 < t0) (ht0_lt : t0 < Real.pi) (hneg : A t0 < 0) :
    HasESEReal A := by
  have hmem : (0 : ℝ) ∈ Set.Icc (A t0) (A 0) := ⟨hneg.le, h0.le⟩
  have hivt := intermediate_value_Icc' ht0_pos.le hcont.continuousOn hmem
  rcases hivt with ⟨τ, ⟨hτ0, hτt0⟩, hAτ⟩
  refine ⟨τ, ?_, lt_of_le_of_lt hτt0 ht0_lt, hAτ⟩
  rcases eq_or_lt_of_le hτ0 with rfl | hpos
  · linarith
  · exact hpos

/-! ### Universal Even-Chain Orthogonality Converse (ALL Even Orders `2n`) -/

/-- For every odd integer `p ≥ 3`, `∫_0^π cos(p t / 2) cos(t / 2) dt = 0`. -/
theorem integral_cos_odd_half_mul_cos_half {p : ℕ} (hp_odd : Odd p) (hp3 : 3 ≤ p) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos ((p : ℝ) * t / 2) * Real.cos (t / 2) = 0 := by
  rcases hp_odd with ⟨m, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hprod : ∀ t : ℝ, Real.cos (((2 * m + 1 : ℕ) : ℝ) * t / 2) * Real.cos (t / 2) =
      (1 / 2 : ℝ) * Real.cos (((m + 1 : ℕ) : ℝ) * t) +
      (1 / 2 : ℝ) * Real.cos ((m : ℝ) * t) := by
    intro t
    have h1 := Real.cos_add (((2 * m + 1 : ℕ) : ℝ) * t / 2) (t / 2)
    have h2 := Real.cos_sub (((2 * m + 1 : ℕ) : ℝ) * t / 2) (t / 2)
    have ha : ((2 * m + 1 : ℕ) : ℝ) * t / 2 + t / 2 = ((m + 1 : ℕ) : ℝ) * t := by
      push_cast; ring
    have hb : ((2 * m + 1 : ℕ) : ℝ) * t / 2 - t / 2 = (m : ℝ) * t := by
      push_cast; ring
    rw [ha] at h1
    rw [hb] at h2
    linarith
  simp_rw [hprod]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) 0 Real.pi)
        (Continuous.intervalIntegrable (by fun_prop) 0 Real.pi),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hint_nat : ∀ k : ℕ, 1 ≤ k → ∫ t in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * t) = 0 := by
    intro k hk
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    have hF : ∀ t ∈ Set.uIcc (0 : ℝ) Real.pi,
        HasDerivAt (fun s => Real.sin ((k : ℝ) * s) / (k : ℝ)) (Real.cos ((k : ℝ) * t)) t := by
      intro t _
      have hd := ((Real.hasDerivAt_sin ((k : ℝ) * t)).comp t
        ((hasDerivAt_id' t).const_mul (k : ℝ))).div_const (k : ℝ)
      refine hd.congr_deriv ?_
      field_simp [hk_ne]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      (Continuous.intervalIntegrable (by fun_prop) 0 Real.pi)]
    simp [Real.sin_nat_mul_pi]
  rw [hint_nat (m + 1) (by omega), hint_nat m hm1]
  ring

/-- Universal Even-Chain ESE Converse: For EVERY even dimension `2n` (`n ≥ 1`), if every
frequency `p k` is an odd natural number `≥ 3` and strictly increasing (so Hochstadt weights
are strictly positive), then `ampEven (fun k => (p k : ℝ))` ALWAYS has Early State Exclusion. -/
theorem even_hasESE_of_min_ge_three {n : ℕ} (hn : 0 < n) (p : Fin n → ℕ)
    (hodd : ∀ k, Odd (p k)) (hge3 : ∀ k, 3 ≤ p k) (hmono : StrictMono p) :
    HasESEReal (ampEven (fun k => (p k : ℝ))) := by
  let pr : Fin n → ℝ := fun k => (p k : ℝ)
  have hw_pos : ∀ k : Fin n, 0 < hochstadtWeightEven pr k := by
    intro k
    unfold hochstadtWeightEven
    refine inv_pos.mpr (mul_pos (by dsimp only [pr]; exact_mod_cast (show 0 < p k by have := hge3 k; omega)) ?_)
    refine Finset.prod_pos fun i hi => abs_pos.mpr ?_
    have hne : i ≠ k := Finset.ne_of_mem_erase hi
    have hpne : p k ≠ p i := fun h => hne (hmono.injective h).symm
    have hpne_r : (p k : ℝ) ≠ (p i : ℝ) := by exact_mod_cast hpne
    have hpos_sum : 0 < (p k : ℝ) + (p i : ℝ) := by
      have h1 : 0 < p k := by have := hge3 k; omega
      have h2 : 0 < p i := by have := hge3 i; omega
      positivity
    intro hzero
    have : ((p k : ℝ) - (p i : ℝ)) * ((p k : ℝ) + (p i : ℝ)) = 0 := by
      calc ((p k : ℝ) - (p i : ℝ)) * ((p k : ℝ) + (p i : ℝ))
          = (p k : ℝ) ^ 2 - (p i : ℝ) ^ 2 := by ring
        _ = 0 := hzero
    rcases mul_eq_zero.mp this with hsub | hsum
    · exact hpne_r (sub_eq_zero.mp hsub)
    · linarith
  have hden_pos : 0 < ∑ k : Fin n, hochstadtWeightEven pr k :=
    Finset.sum_pos (fun k _ => hw_pos k) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have hcont : Continuous (ampEven pr) := by
    unfold ampEven
    fun_prop
  have hA0 : ampEven pr 0 = 1 := by
    unfold ampEven
    simp [div_self hden_pos.ne']
  have hint_zero : ∫ t in (0 : ℝ)..Real.pi, ampEven pr t * Real.cos (t / 2) = 0 := by
    have hrewrite : ∀ t : ℝ, ampEven pr t * Real.cos (t / 2) =
        (∑ k : Fin n, hochstadtWeightEven pr k * (Real.cos ((p k : ℝ) * t / 2) * Real.cos (t / 2))) /
          (∑ k : Fin n, hochstadtWeightEven pr k) := by
      intro t
      unfold ampEven
      rw [div_mul_eq_mul_div, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hrewrite]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
    · have hzero_sum : ∑ k : Fin n,
          ∫ t in (0 : ℝ)..Real.pi, hochstadtWeightEven pr k *
            (Real.cos ((p k : ℝ) * t / 2) * Real.cos (t / 2)) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [intervalIntegral.integral_const_mul,
            integral_cos_odd_half_mul_cos_half (hodd k) (hge3 k), mul_zero]
      rw [hzero_sum, zero_div]
    · intro k _
      exact (by fun_prop : Continuous _).intervalIntegrable 0 Real.pi
  -- By contradiction, if `ampEven pr t ≥ 0` on all of `(0, π)`, then `∫_0^π ampEven(t) cos(t/2) dt > 0`.
  by_contra hno
  have hnonneg : ∀ t ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ ampEven pr t * Real.cos (t / 2) := by
    intro t ht
    have hcos_nn : 0 ≤ Real.cos (t / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩
    have hA_nn : 0 ≤ ampEven pr t := by
      by_contra hlt
      push Not at hlt
      have ht_pos : 0 < t := by
        rcases eq_or_lt_of_le ht.1 with rfl | hp
        · linarith
        · exact hp
      have ht_lt : t < Real.pi := by
        rcases eq_or_lt_of_le ht.2 with rfl | hlt_pi
        · have hApi : ampEven pr Real.pi = 0 := by
            unfold ampEven
            have hsum0 : ∑ k : Fin n, hochstadtWeightEven pr k * Real.cos (pr k * Real.pi / 2) = 0 := by
              refine Finset.sum_eq_zero fun k _ => ?_
              rcases hodd k with ⟨m, hm⟩
              have harg : pr k * Real.pi / 2 = (m : ℝ) * Real.pi + Real.pi / 2 := by
                simp only [pr, hm]; push_cast; ring
              rw [harg, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero, mul_zero]
            rw [hsum0, zero_div]
          linarith
        · exact hlt_pi
      exact hno (hasESEReal_of_pos_zero_neg_pt hcont (by linarith) ht_pos ht_lt hlt)
    exact mul_nonneg hA_nn hcos_nn
  have hpos_int : 0 < ∫ t in (0 : ℝ)..Real.pi, ampEven pr t * Real.cos (t / 2) := by
    refine intervalIntegral.integral_pos Real.pi_pos
      (hcont.mul (Real.continuous_cos.comp (continuous_id.div_const 2))).continuousOn
      (fun t ht => hnonneg t ⟨ht.1.le, ht.2⟩) ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, ?_⟩
    simp [hA0]
  linarith

/-! ### Theorem 1: Complete `4 × 4` Symmetric PST Dichotomy -/

/-- Forward `4 × 4`: For EVERY real `q > 1` with `q` odd and `q - 1 ≡ 2 (mod 4)` (i.e. `q ≡ 3 (mod 4)`),
`amp4 1 q t > 0` for all `t ∈ [0, π)`, hence NO ESE. -/
theorem amp4_pos_of_p_eq_one {q : ℕ} (hq_mod : q % 4 = 3) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t < Real.pi) : 0 < amp4 1 (q : ℝ) t := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    have : 1 < q := by omega
    exact_mod_cast this
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · unfold amp4
    simp only [mul_zero, zero_div, Real.cos_zero, mul_one]
    have hden : 0 < (1 : ℝ) + (q : ℝ) := by linarith
    have hcomm : (q : ℝ) + 1 = 1 + (q : ℝ) := by ring
    rw [hcomm, div_self hden.ne']
    norm_num
  · set u := (Real.pi - t) / 2
    have hu0 : 0 < u := by simp only [u]; linarith
    have hu : u < Real.pi / 2 := by simp only [u]; linarith
    have ht_eq : t = Real.pi - 2 * u := by simp only [u]; ring
    rw [ht_eq]
    unfold amp4
    have hcos1 : Real.cos (1 * (Real.pi - 2 * u) / 2) = Real.sin u := by
      have : 1 * (Real.pi - 2 * u) / 2 = Real.pi / 2 - u := by ring
      rw [this, Real.cos_pi_div_two_sub]
    have hcosq : Real.cos ((q : ℝ) * (Real.pi - 2 * u) / 2) = -Real.sin ((q : ℝ) * u) := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 4 * k + 3 := ⟨q / 4, by omega⟩
      have harg : (q : ℝ) * (Real.pi - 2 * u) / 2 =
          (Real.pi / 2 - (q : ℝ) * u) + Real.pi + (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; push_cast; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, Real.cos_pi_div_two_sub]
    rw [hcos1, hcosq]
    have hden : 0 < (1 : ℝ) + (q : ℝ) := by linarith
    refine div_pos ?_ hden
    have habs := abs_sin_mul_lt_mul_sin hq1 hu0 hu
    have hle : Real.sin ((q : ℝ) * u) ≤ |Real.sin ((q : ℝ) * u)| := le_abs_self _
    linarith

/-- Theorem 1 (Complete `4 × 4` Dichotomy): For any reduced `4 × 4` symmetric PST spectrum
`{±p/2, ±q/2}` (`p < q` odd, `(q - p) % 4 = 2`, `gcd(p, q) = 1`),
`¬HasESEReal (amp4 p q) ↔ p = 1`. -/
theorem dichotomy_4x4 {p q : ℕ} (hp_odd : Odd p) (hq_odd : Odd q) (hpq : p < q)
    (hgap : (q - p) % 4 = 2) :
    ¬HasESEReal (amp4 (p : ℝ) (q : ℝ)) ↔ p = 1 := by
  constructor
  · intro hno
    by_contra hp1
    have hp3 : 3 ≤ p := by
      rcases hp_odd with ⟨m, rfl⟩
      omega
    have hq3 : 3 ≤ q := by omega
    have hese := even_hasESE_of_min_ge_three (n := 2) (by norm_num) ![p, q]
      (fun k => by fin_cases k <;> assumption)
      (fun k => by fin_cases k <;> assumption)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    rcases hese with ⟨τ, hτ0, hτpi, hzero⟩
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    have hpq_r : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
    have heq : ampEven (fun k : Fin 2 => (![p, q] k : ℝ)) τ = amp4 (p : ℝ) (q : ℝ) τ := by
      have hfun : (fun k : Fin 2 => (![p, q] k : ℝ)) = ![(p : ℝ), (q : ℝ)] := by
        ext k; fin_cases k <;> rfl
      rw [hfun, ampEven_two_eq_amp4 hp_pos hpq_r]
    rw [heq] at hzero
    exact hno ⟨τ, hτ0, hτpi, hzero⟩
  · rintro rfl
    have hq_mod : q % 4 = 3 := by omega
    rintro ⟨τ, hτ0, hτpi, hzero⟩
    have hpos := amp4_pos_of_p_eq_one hq_mod hτ0.le hτpi
    simp only [Nat.cast_one] at hzero
    linarith

/-! ### Theorem 2: Complete `5 × 5` Symmetric PST Dichotomy (Enriquez-Minenkova 2026) -/

/-- Exact cancellation-free `sin²` representation for `5 × 5` symmetric PST amplitude
(`y` odd, `x` even). -/
theorem amp5_pi_sub_two_mul {y x : ℕ} (hy_odd : Odd y) (hx_even : Even x)
    (hy0 : 0 < y) (hyx : y < x) (u : ℝ) :
    amp5 (y : ℝ) (x : ℝ) (Real.pi - 2 * u) =
      (2 * ((x : ℝ) ^ 2 * Real.sin ((y : ℝ) * u) ^ 2 -
            (y : ℝ) ^ 2 * Real.sin ((x : ℝ) * u) ^ 2)) /
        (2 * (x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) *
        ((x : ℝ) ^ 2 - (y : ℝ) ^ 2) := by
  have hy_r : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy0
  have hyx_r : (y : ℝ) < (x : ℝ) := by exact_mod_cast hyx
  have hxy2 : (0 : ℝ) < (x : ℝ) ^ 2 - (y : ℝ) ^ 2 := by nlinarith
  have hx_r : (0 : ℝ) < (x : ℝ) := by linarith
  have hcosy : Real.cos ((y : ℝ) * (Real.pi - 2 * u)) = -Real.cos (2 * ((y : ℝ) * u)) := by
    rcases hy_odd with ⟨m, rfl⟩
    have harg : ((2 * m + 1 : ℕ) : ℝ) * (Real.pi - 2 * u) =
        -(2 * (((2 * m + 1 : ℕ) : ℝ) * u)) + Real.pi + (m : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, Real.cos_neg]
  have hcosx : Real.cos ((x : ℝ) * (Real.pi - 2 * u)) = Real.cos (2 * ((x : ℝ) * u)) := by
    rcases hx_even with ⟨m, rfl⟩
    have harg : ((m + m : ℕ) : ℝ) * (Real.pi - 2 * u) =
        -(2 * (((m + m : ℕ) : ℝ) * u)) + (m : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_neg]
  unfold amp5
  rw [hcosy, hcosx, Real.cos_two_mul, Real.cos_two_mul]
  have hsy := Real.sin_sq_add_cos_sq ((y : ℝ) * u)
  have hsx := Real.sin_sq_add_cos_sq ((x : ℝ) * u)
  have hcy : Real.cos ((y : ℝ) * u) ^ 2 = 1 - Real.sin ((y : ℝ) * u) ^ 2 := by linarith
  have hcx : Real.cos ((x : ℝ) * u) ^ 2 = 1 - Real.sin ((x : ℝ) * u) ^ 2 := by linarith
  rw [hcy, hcx]
  field_simp [hy_r.ne', hx_r.ne', hxy2.ne']
  ring

/-- Theorem 2 (Complete `5 × 5` Dichotomy): For any reduced `5 × 5` symmetric PST spectrum
`{0, ±y, ±x}` (`0 < y < x`, `y` odd, `x` even, `gcd(y, x) = 1`),
`¬HasESEReal (amp5 y x) ↔ y = 1`. -/
theorem dichotomy_5x5 {y x : ℕ} (hy_odd : Odd y) (hx_even : Even x)
    (hyx : y < x) (hcop : Nat.Coprime y x) :
    ¬HasESEReal (amp5 (y : ℝ) (x : ℝ)) ↔ y = 1 := by
  have hy0 : 0 < y := by rcases hy_odd with ⟨m, rfl⟩; omega
  have hy_r : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy0
  have hyx_r : (y : ℝ) < (x : ℝ) := by exact_mod_cast hyx
  have hx_r : (0 : ℝ) < (x : ℝ) := by linarith
  have hxy2 : (0 : ℝ) < (x : ℝ) ^ 2 - (y : ℝ) ^ 2 := by nlinarith
  constructor
  · intro hno
    by_contra hy1
    have hy3 : 3 ≤ y := by rcases hy_odd with ⟨m, rfl⟩; omega
    -- Evaluate at the explicit interior witness `t0 = π / y ∈ (0, π)`!
    set t0 : ℝ := Real.pi / (y : ℝ)
    have ht0_pos : 0 < t0 := div_pos Real.pi_pos hy_r
    have ht0_lt : t0 < Real.pi := by
      have hy_gt1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (show 1 < y by omega)
      exact (div_lt_iff₀ hy_r).mpr (by nlinarith [Real.pi_pos])
    have hcont : Continuous (amp5 (y : ℝ) (x : ℝ)) := by unfold amp5; fun_prop
    have hA0 : 0 < amp5 (y : ℝ) (x : ℝ) 0 := by
      unfold amp5
      simp only [mul_zero, Real.cos_zero, mul_one]
      have hden : 0 < 1 / ((y : ℝ) ^ 2 * (x : ℝ) ^ 2) +
          1 / ((y : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) +
          1 / ((x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) := by positivity
      rw [div_self hden.ne']
      norm_num
    have hneg : amp5 (y : ℝ) (x : ℝ) t0 < 0 := by
      unfold amp5
      have hden : 0 < 1 / ((y : ℝ) ^ 2 * (x : ℝ) ^ 2) +
          1 / ((y : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) +
          1 / ((x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) := by positivity
      refine div_neg_of_neg_of_pos ?_ hden
      have hcy : Real.cos ((y : ℝ) * t0) = -1 := by
        have : (y : ℝ) * t0 = Real.pi := mul_div_cancel₀ Real.pi hy_r.ne'
        rw [this, Real.cos_pi]
      rw [hcy]
      have hnum_eq :
          1 / ((y : ℝ) ^ 2 * (x : ℝ) ^ 2) +
          1 / ((y : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) * (-1) +
          1 / ((x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) * Real.cos ((x : ℝ) * t0) =
          -(1 - Real.cos ((x : ℝ) * t0)) / ((x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - (y : ℝ) ^ 2)) := by
        field_simp [hy_r.ne', hx_r.ne', hxy2.ne']
        ring
      rw [hnum_eq]
      have hcos_lt_one : Real.cos ((x : ℝ) * t0) < 1 := by
        by_contra hge
        push Not at hge
        have hcos1 : Real.cos ((x : ℝ) * t0) = 1 := le_antisymm (Real.cos_le_one _) hge
        rw [Real.cos_eq_one_iff] at hcos1
        rcases hcos1 with ⟨k, hk⟩
        have hmul : (x : ℝ) * Real.pi = (2 * k : ℝ) * (y : ℝ) * Real.pi := by
          have : (x : ℝ) * (Real.pi / (y : ℝ)) = (k : ℝ) * (2 * Real.pi) := hk.symm
          have h1 := congrArg (· * (y : ℝ)) this
          have h1' : (x : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) * (y : ℝ) := by
            have hlhs : (x : ℝ) * (Real.pi / (y : ℝ)) * (y : ℝ) = (x : ℝ) * Real.pi := by
              field_simp [hy_r.ne']
            linarith
          linarith
        have hx_eq : (x : ℝ) = (2 * k : ℝ) * (y : ℝ) := mul_right_cancel₀ Real.pi_ne_zero hmul
        have hk_nonneg : 0 ≤ k := by
          by_contra hkn
          push Not at hkn
          have : (2 * k : ℝ) * (y : ℝ) < 0 := by
            have hk_r : (k : ℝ) < 0 := by exact_mod_cast hkn
            nlinarith
          linarith
        lift k to ℕ using hk_nonneg
        have hx_nat : x = 2 * k * y := by
          have hx_r_eq : (x : ℝ) = ((2 * k * y : ℕ) : ℝ) := by
            push_cast at hx_eq ⊢
            linarith
          exact_mod_cast hx_r_eq
        have hdvd : y ∣ x := ⟨2 * k, by linarith⟩
        have h1 := hcop.eq_one_of_dvd hdvd
        exact hy1 h1
      exact div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact hno (hasESEReal_of_pos_zero_neg_pt hcont hA0 ht0_pos ht0_lt hneg)
  · rintro rfl
    rintro ⟨τ, hτ0, hτpi, hzero⟩
    set u := (Real.pi - τ) / 2
    have hu0 : 0 < u := by simp only [u]; linarith
    have hu : u < Real.pi / 2 := by simp only [u]; linarith
    have hτ_eq : τ = Real.pi - 2 * u := by simp only [u]; ring
    rw [hτ_eq, amp5_pi_sub_two_mul hy_odd hx_even hy0 hyx u] at hzero
    simp only [Nat.cast_one, one_mul, one_pow] at hzero
    have hx_gt1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hyx
    have hpos : 0 < (2 * ((x : ℝ) ^ 2 * Real.sin u ^ 2 - 1 * Real.sin ((x : ℝ) * u) ^ 2)) /
        (2 * (x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - 1)) * ((x : ℝ) ^ 2 - 1) := by
      have hsin := sin_sq_mul_lt_mul_sq_sin_sq hx_gt1 hu0 hu
      have hfac : 0 < (x : ℝ) ^ 2 - 1 := by nlinarith
      have hden : 0 < 2 * (x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - 1) := mul_pos (by positivity) hfac
      exact mul_pos (div_pos (by linarith) hden) hfac
    have hzero' : (2 * ((x : ℝ) ^ 2 * Real.sin u ^ 2 - 1 * Real.sin ((x : ℝ) * u) ^ 2)) /
        (2 * (x : ℝ) ^ 2 * ((x : ℝ) ^ 2 - 1)) * ((x : ℝ) ^ 2 - 1) = 0 := by
      simpa using hzero
    linarith

/-! ### Theorem 3: Complete `6 × 6` Critical Even Dichotomy (BRAND NEW) -/

/-- Exact spherical-Bessel divided-difference identity for `6 × 6` with `p = 1`, `q ≡ 3 (mod 4)`,
`r ≡ 1 (mod 4)`. -/
theorem amp6_pos_of_p_eq_one {q r : ℕ} (hq_mod : q % 4 = 3) (hr_mod : r % 4 = 1)
    (h1q : 1 < q) (hqr : q < r) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < Real.pi) :
    0 < amp6 1 (q : ℝ) (r : ℝ) t := by
  have hq_r : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h1q
  have hr_r : (q : ℝ) < (r : ℝ) := by exact_mod_cast hqr
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) ^ 2 - 1 := by nlinarith
  have hr1 : (0 : ℝ) < (r : ℝ) ^ 2 - 1 := by nlinarith
  have hrq : (0 : ℝ) < (r : ℝ) ^ 2 - (q : ℝ) ^ 2 := by nlinarith
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · unfold amp6
    simp only [mul_zero, zero_div, Real.cos_zero, mul_one]
    have hden : 0 < 1 / (1 * ((q : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - 1 ^ 2)) +
        1 / ((q : ℝ) * ((q : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) +
        1 / ((r : ℝ) * ((r : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) := by
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
    unfold amp6
    have hden : 0 < 1 / (1 * ((q : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - 1 ^ 2)) +
        1 / ((q : ℝ) * ((q : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) +
        1 / ((r : ℝ) * ((r : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) := by
      have : (1 : ℝ) ^ 2 = 1 := one_pow 2
      rw [this]; positivity
    refine div_pos ?_ hden
    have hc1 : Real.cos (1 * (Real.pi - 2 * u) / 2) = Real.sin u := by
      have : 1 * (Real.pi - 2 * u) / 2 = Real.pi / 2 - u := by ring
      rw [this, Real.cos_pi_div_two_sub]
    have hcq : Real.cos ((q : ℝ) * (Real.pi - 2 * u) / 2) = -Real.sin ((q : ℝ) * u) := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 4 * k + 3 := ⟨q / 4, by omega⟩
      have harg : (q : ℝ) * (Real.pi - 2 * u) / 2 =
          (Real.pi / 2 - (q : ℝ) * u) + Real.pi + (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; push_cast; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, Real.cos_pi_div_two_sub]
    have hcr : Real.cos ((r : ℝ) * (Real.pi - 2 * u) / 2) = Real.sin ((r : ℝ) * u) := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, r = 4 * k + 1 := ⟨r / 4, by omega⟩
      have harg : (r : ℝ) * (Real.pi - 2 * u) / 2 =
          (Real.pi / 2 - (r : ℝ) * u) + (k : ℝ) * (2 * Real.pi) := by
        rw [hk]; push_cast; ring
      rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two_sub]
    rw [hc1, hcq, hcr]
    -- Rewrite numerator directly as `u^3 / (r^2 - q^2) * [slope(u^2, (q u)^2) - slope(u^2, (r u)^2)]`!
    have hHe1 : Real.sin u = u * He (u ^ 2) := by
      rw [He_sq hu0]; field_simp [hu0.ne']
    have hHeq : Real.sin ((q : ℝ) * u) = (q : ℝ) * u * He (((q : ℝ) * u) ^ 2) := by
      rw [He_sq (mul_pos hq0 hu0)]; field_simp [hq0.ne', hu0.ne']
    have hHer : Real.sin ((r : ℝ) * u) = (r : ℝ) * u * He (((r : ℝ) * u) ^ 2) := by
      rw [He_sq (mul_pos hr0 hu0)]; field_simp [hr0.ne', hu0.ne']
    rw [hHe1, hHeq, hHer]
    have hqu_lt : u ^ 2 < ((q : ℝ) * u) ^ 2 := by
      have : ((q : ℝ) * u) ^ 2 - u ^ 2 = ((q : ℝ) ^ 2 - 1) * u ^ 2 := by ring
      nlinarith [mul_pos hq1 hu2]
    have hqru_lt : ((q : ℝ) * u) ^ 2 < ((r : ℝ) * u) ^ 2 := by
      have : ((r : ℝ) * u) ^ 2 - ((q : ℝ) * u) ^ 2 = ((r : ℝ) ^ 2 - (q : ℝ) ^ 2) * u ^ 2 := by ring
      nlinarith [mul_pos hrq hu2]
    have hslope := He_slope_strictAnti hu0 hu hqu_lt hqru_lt
    have hid :
        1 / (1 * ((q : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - 1 ^ 2)) * (u * He (u ^ 2)) +
        1 / ((q : ℝ) * ((q : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) *
          -((q : ℝ) * u * He (((q : ℝ) * u) ^ 2)) +
        1 / ((r : ℝ) * ((r : ℝ) ^ 2 - 1 ^ 2) * ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) *
          ((r : ℝ) * u * He (((r : ℝ) * u) ^ 2)) =
        (u ^ 3 / ((r : ℝ) ^ 2 - (q : ℝ) ^ 2)) *
          ((He (u ^ 2) - He (((q : ℝ) * u) ^ 2)) / (((q : ℝ) * u) ^ 2 - u ^ 2) -
           (He (u ^ 2) - He (((r : ℝ) * u) ^ 2)) / (((r : ℝ) * u) ^ 2 - u ^ 2)) := by
      have hqu_sub : ((q : ℝ) * u) ^ 2 - u ^ 2 ≠ 0 := (sub_pos.mpr hqu_lt).ne'
      have hru_sub : ((r : ℝ) * u) ^ 2 - u ^ 2 ≠ 0 := (sub_pos.mpr (lt_trans hqu_lt hqru_lt)).ne'
      field_simp [hq0.ne', hr0.ne', hq1.ne', hr1.ne', hrq.ne', hqu_sub, hru_sub]
      ring
    rw [hid]
    exact mul_pos (div_pos (pow_pos hu0 3) hrq) (sub_pos.mpr hslope)

/-- Theorem 3 (Complete `6 × 6` Critical Even Dichotomy): For any reduced `6 × 6` symmetric PST
spectrum `{±p/2, ±q/2, ±r/2}` (`p < q < r` odd, `(q - p) % 4 = 2`, `(r - q) % 4 = 2`),
`¬HasESEReal (amp6 p q r) ↔ p = 1`. -/
theorem dichotomy_6x6 {p q r : ℕ} (hp_odd : Odd p) (hq_odd : Odd q) (hr_odd : Odd r)
    (hpq : p < q) (hqr : q < r) (hgap1 : (q - p) % 4 = 2) (hgap2 : (r - q) % 4 = 2) :
    ¬HasESEReal (amp6 (p : ℝ) (q : ℝ) (r : ℝ)) ↔ p = 1 := by
  constructor
  · intro hno
    by_contra hp1
    have hp3 : 3 ≤ p := by rcases hp_odd with ⟨m, rfl⟩; omega
    have hq3 : 3 ≤ q := by omega
    have hr3 : 3 ≤ r := by omega
    have hese := even_hasESE_of_min_ge_three (n := 3) (by norm_num) ![p, q, r]
      (fun k => by fin_cases k <;> assumption)
      (fun k => by fin_cases k <;> assumption)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> (simp_all; try omega))
    rcases hese with ⟨τ, hτ0, hτpi, hzero⟩
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    have hpq_r : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
    have hqr_r : (q : ℝ) < (r : ℝ) := by exact_mod_cast hqr
    have heq : ampEven (fun k : Fin 3 => (![p, q, r] k : ℝ)) τ = amp6 (p : ℝ) (q : ℝ) (r : ℝ) τ := by
      have hfun : (fun k : Fin 3 => (![p, q, r] k : ℝ)) = ![(p : ℝ), (q : ℝ), (r : ℝ)] := by
        ext k; fin_cases k <;> rfl
      rw [hfun, ampEven_three_eq_amp6 hp_pos hpq_r hqr_r]
    rw [heq] at hzero
    exact hno ⟨τ, hτ0, hτpi, hzero⟩
  · rintro rfl
    have hq_mod : q % 4 = 3 := by omega
    have hr_mod : r % 4 = 1 := by omega
    rintro ⟨τ, hτ0, hτpi, hzero⟩
    have hpos := amp6_pos_of_p_eq_one hq_mod hr_mod hpq hqr hτ0.le hτpi
    simp only [Nat.cast_one] at hzero
    linarith

end SpectralEclipse
