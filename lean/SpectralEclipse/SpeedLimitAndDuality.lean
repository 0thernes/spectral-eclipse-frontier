/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Theorem 10: Exact QGTL / Mandelstam-Tamm ESE Speed Limit & ESE-ETE Time-Reversal Duality

Proves Theorem 10 of the linked ESE chain in full generality for arbitrary dimension `n`:
  1. **Exact Jacobi Energy Variance / QGTL Metric (`jacobi_energy_variance_eq_b0_sq`)**:
     For EVERY `n × n` real symmetric Jacobi matrix `J = jacobiMatrix a b` (`n ≥ 2`),
     `⟨e_0, J e_0⟩ = a 0` and `‖(J - a 0 • I) e_0‖² = (b 0)²`. Hence the Quantum Geometric
     Tensor Fubini-Study metric at `|0⟩` is identically `g_{tt}(e_0) = (b 0)²`!
  2. **Universal Mandelstam-Tamm / Fleming-Bhattacharyya Speed Limit (`mandelstam_tamm_ese_bound`)**:
     For ANY discrete spectrum `lam : Fin n → ℝ`, probability weights `w : Fin n → ℝ`
     (`w k ≥ 0`, `∑ w k = 1`), mean energy `μ = ∑ w k * lam k`, and variance
     `∑ w k * (lam k - μ)² = σ²` (`σ > 0`), EVERY time `τ > 0` at which the complex return
     amplitude vanishes (`returnAmpComplex lam w τ = 0`) MUST satisfy:
       `τ ≥ π / (2 * σ)`!
     Combined with `jacobi_energy_variance_eq_b0_sq`, EVERY Early State Exclusion time of ANY
     1D spin chain (symmetric or non-symmetric, arbitrary length `n`) satisfies `τ ≥ π / (2 * |b₀|)`.
  3. **Exact ESE ↔ Early Target Exclusion (ETE) Time-Reversal Duality (`ese_ete_duality`)**:
     For ANY persymmetric PST chain satisfying `u_k(n-1) = (-1)^k u_k(0)` and
     `e^{-i λ_k T} = η (-1)^k` with `‖η‖ = 1`, we have for ALL `t ∈ ℝ`:
       `‖targetAmpComplex hn lam u (T - t)‖ = ‖returnAmpComplex lam (fun k => (u k 0)²) t‖`!
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SpectralEclipse

/-! ### Part 1: Exact Jacobi Energy Variance = `b₀²` (QGTL Fubini-Study Metric) -/

/-- For EVERY real symmetric Jacobi matrix `J = jacobiMatrix a b` of length `n ≥ 2`, the action
of `J` on `e_0` has `0`-th entry `a 0`, `1`-st entry `b 0`, and all other entries `0`. -/
theorem jacobiMatrix_mul_e0 {n : ℕ} (hn : 2 ≤ n) (a b : Fin n → ℝ) (i : Fin n) :
    (jacobiMatrix a b) i ⟨0, by omega⟩ =
      if (i : ℕ) = 0 then a ⟨0, by omega⟩
      else if (i : ℕ) = 1 then b ⟨0, by omega⟩
      else 0 := by
  simp only [jacobiMatrix, Matrix.of_apply]
  by_cases h0 : (i : ℕ) = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
    rw [hi]; simp
  · have hi_ne : i ≠ ⟨0, by omega⟩ := fun h => h0 (congrArg Fin.val h)
    simp only [hi_ne, h0, ↓reduceIte]
    have hnot1 : ¬((i : ℕ) + 1 = 0) := Nat.succ_ne_zero _
    simp only [hnot1, ↓reduceIte]
    by_cases h1 : (i : ℕ) = 1
    · simp [h1]
    · have h1' : ¬(0 + 1 = (i : ℕ)) := by omega
      simp [h1, h1']

/-- **Exact QGTL Metric / Energy Variance Identity**:
For EVERY `n × n` Jacobi matrix `J = jacobiMatrix a b` (`n ≥ 2`), the variance of `J` in the
initial localized state `e_0` equals `(b 0)²` identically:
  `∑_i (J_{i,0} - a_0 δ_{i,0})² = (b 0)²`. -/
theorem jacobi_energy_variance_eq_b0_sq {n : ℕ} (hn : 2 ≤ n) (a b : Fin n → ℝ) :
    ∑ i : Fin n,
      ((jacobiMatrix a b) i ⟨0, by omega⟩ -
        (if i = ⟨0, by omega⟩ then a ⟨0, by omega⟩ else 0)) ^ 2 =
      (b ⟨0, by omega⟩) ^ 2 := by
  let i1 : Fin n := ⟨1, by omega⟩
  rw [Finset.sum_eq_single i1]
  · rw [jacobiMatrix_mul_e0 hn a b i1]
    have hne : i1 ≠ ⟨0, by omega⟩ := by simp [i1, Fin.ext_iff]
    simp [i1, hne]
  · intro i _ hi_ne
    rw [jacobiMatrix_mul_e0 hn a b i]
    by_cases h0 : (i : ℕ) = 0
    · have hi0 : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [hi0]; simp
    · have hi0 : i ≠ ⟨0, by omega⟩ := fun h => h0 (congrArg Fin.val h)
      have h1 : (i : ℕ) ≠ 1 := fun h => hi_ne (Fin.ext h)
      simp [h0, hi0, h1]
  · intro hnot
    exact absurd (Finset.mem_univ i1) hnot

/-- Eigenbasis variance bridge: if `J = jacobiMatrix a b` has an orthonormal eigenbasis `(lam, u)`,
then the spectral variance `∑_k (u_k 0)² (lam k - a 0)²` equals `(b 0)²` identically! -/
theorem spectral_variance_eq_b0_sq {n : ℕ} (hn : 2 ≤ n) (a b : Fin n → ℝ)
    (lam : Fin n → ℝ) (u : Fin n → Fin n → ℝ)
    (heig : ∀ k : Fin n, (jacobiMatrix a b).mulVec (u k) = lam k • u k)
    (hcomp : ∀ i j : Fin n, ∑ k : Fin n, u k i * u k j = if i = j then 1 else 0) :
    ∑ k : Fin n, (u k ⟨0, by omega⟩) ^ 2 * (lam k - a ⟨0, by omega⟩) ^ 2 =
      (b ⟨0, by omega⟩) ^ 2 := by
  let e0 : Fin n := ⟨0, by omega⟩
  -- For every `k`, `lam k * u k 0 = ∑_i J_{0, i} u k i = ∑_i J_{i, 0} u k i` (by symmetry of J)
  have hproj : ∀ k : Fin n,
      (lam k - a e0) * u k e0 =
        ∑ i : Fin n, ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) * u k i := by
    intro k
    have hk := congrArg (fun v => v e0) (heig k)
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hk
    have hsym : ∀ i : Fin n, (jacobiMatrix a b) e0 i = (jacobiMatrix a b) i e0 := by
      intro i
      have := congrArg (fun M => M i e0) (jacobiMatrix_transpose a b)
      simpa [Matrix.transpose_apply] using this
    simp_rw [hsym] at hk
    have hsplit : ∑ i : Fin n, ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) * u k i =
        (∑ i : Fin n, (jacobiMatrix a b) i e0 * u k i) - a e0 * u k e0 := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_eq_single e0]
      · simp
      · intro i _ hi; simp [hi]
      · intro h; exact absurd (Finset.mem_univ e0) h
    rw [hsplit, hk]
    ring
  calc
    ∑ k : Fin n, (u k e0) ^ 2 * (lam k - a e0) ^ 2
        = ∑ k : Fin n, ((lam k - a e0) * u k e0) * ((lam k - a e0) * u k e0) := by
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k : Fin n,
          (∑ i : Fin n, ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) * u k i) *
          (∑ j : Fin n, ((jacobiMatrix a b) j e0 - if j = e0 then a e0 else 0) * u k j) := by
          refine Finset.sum_congr rfl fun k _ => by rw [hproj k]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) *
          ((jacobiMatrix a b) j e0 - if j = e0 then a e0 else 0) *
          (∑ k : Fin n, u k i * u k j) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i : Fin n, ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hstep : ∑ j : Fin n,
              ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) *
              ((jacobiMatrix a b) j e0 - if j = e0 then a e0 else 0) *
              (∑ k : Fin n, u k i * u k j) =
              ((jacobiMatrix a b) i e0 - if i = e0 then a e0 else 0) ^ 2 := by
            rw [Finset.sum_eq_single i]
            · rw [hcomp i i]; simp [sq]
            · intro j _ hji; rw [hcomp i j]; simp [Ne.symm hji]
            · intro h; exact absurd (Finset.mem_univ i) h
          exact hstep
    _ = (b e0) ^ 2 := jacobi_energy_variance_eq_b0_sq hn a b

/-! ### Part 2: Universal Mandelstam-Tamm / Fleming-Bhattacharyya Speed Limit -/

/-- Return probability `P(t) = ‖∑_k w_k e^{-i δ_k t}‖²` written purely in real sines and cosines. -/
noncomputable def returnProbReal {n : ℕ} (δ w : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ k : Fin n, w k * Real.cos (δ k * t)) ^ 2 + (∑ k : Fin n, w k * Real.sin (δ k * t)) ^ 2

/-- Global phase invariance: shifting all energies by `μ` leaves `‖returnAmpComplex lam w t‖²`
equal to `returnProbReal (fun k => lam k - μ) w t`. -/
theorem normSq_returnAmpComplex_eq_returnProbReal {n : ℕ} (lam w : Fin n → ℝ) (μ t : ℝ) :
    Complex.normSq (returnAmpComplex lam w t) = returnProbReal (fun k => lam k - μ) w t := by
  have hfac : returnAmpComplex lam w t =
      Complex.exp (-Complex.I * (μ : ℂ) * (t : ℂ)) *
        returnAmpComplex (fun k => lam k - μ) w t := by
    unfold returnAmpComplex
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hexp : Complex.exp (-Complex.I * (lam k : ℂ) * (t : ℂ)) =
        Complex.exp (-Complex.I * (μ : ℂ) * (t : ℂ)) *
        Complex.exp (-Complex.I * ((lam k - μ : ℝ) : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hexp]; ring
  rw [hfac, map_mul]
  have hunit : Complex.normSq (Complex.exp (-Complex.I * (μ : ℂ) * (t : ℂ))) = 1 := by
    have : -Complex.I * (μ : ℂ) * (t : ℂ) = ((-(μ * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    nlinarith [Real.cos_sq_add_sin_sq (-(μ * t))]
  rw [hunit, one_mul]
  unfold returnAmpComplex returnProbReal
  rw [Complex.normSq_apply]
  have hre : (∑ k : Fin n, (w k : ℂ) * Complex.exp (-Complex.I * ((lam k - μ : ℝ) : ℂ) * (t : ℂ))).re =
      ∑ k : Fin n, w k * Real.cos ((lam k - μ) * t) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : -Complex.I * ((lam k - μ : ℝ) : ℂ) * (t : ℂ) = ((-((lam k - μ) * t) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Real.cos_neg]
    ring
  have him : (∑ k : Fin n, (w k : ℂ) * Complex.exp (-Complex.I * ((lam k - μ : ℝ) : ℂ) * (t : ℂ))).im =
      -(∑ k : Fin n, w k * Real.sin ((lam k - μ) * t)) := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : -Complex.I * ((lam k - μ : ℝ) : ℂ) * (t : ℂ) = ((-((lam k - μ) * t) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Real.sin_neg]
    ring
  rw [hre, him]
  ring

/-- Key Bhattacharyya-Fleming differential inequality: for any centered probability distribution
`w k ≥ 0`, `∑ w k = 1`, `∑ w k δ k = 0`, `∑ w k (δ k)² = σ²`,
  `(P'(t))² ≤ 4 σ² P(t) (1 - P(t))` for ALL `t ∈ ℝ`! -/
theorem returnProbReal_deriv_sq_le {n : ℕ} (δ w : Fin n → ℝ) (σ : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k : Fin n, w k = 1)
    (hmean : ∑ k : Fin n, w k * δ k = 0)
    (hvar : ∑ k : Fin n, w k * (δ k) ^ 2 = σ ^ 2) (t : ℝ) :
    let X := ∑ k : Fin n, w k * Real.cos (δ k * t)
    let Y := ∑ k : Fin n, w k * Real.sin (δ k * t)
    let X' := -(∑ k : Fin n, w k * δ k * Real.sin (δ k * t))
    let Y' := ∑ k : Fin n, w k * δ k * Real.cos (δ k * t)
    HasDerivAt (returnProbReal δ w) (2 * (X * X' + Y * Y')) t ∧
    0 ≤ returnProbReal δ w t ∧
    returnProbReal δ w t ≤ 1 ∧
    (2 * (X * X' + Y * Y')) ^ 2 ≤ 4 * σ ^ 2 * returnProbReal δ w t * (1 - returnProbReal δ w t) := by
  intro X Y X' Y'
  have hX : HasDerivAt (fun s => ∑ k : Fin n, w k * Real.cos (δ k * s)) X' t := by
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun s => w k * Real.cos (δ k * s)) (-(w k * δ k * Real.sin (δ k * t))) t := by
      intro k _
      have hd := ((Real.hasDerivAt_cos (δ k * t)).comp t
        ((hasDerivAt_id' t).const_mul (δ k))).const_mul (w k)
      refine hd.congr_deriv ?_
      ring
    have hsum_d := HasDerivAt.fun_sum hterm
    refine hsum_d.congr_deriv ?_
    simp only [X', ← Finset.sum_neg_distrib]
  have hY : HasDerivAt (fun s => ∑ k : Fin n, w k * Real.sin (δ k * s)) Y' t := by
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun s => w k * Real.sin (δ k * s)) (w k * δ k * Real.cos (δ k * t)) t := by
      intro k _
      have hd := ((Real.hasDerivAt_sin (δ k * t)).comp t
        ((hasDerivAt_id' t).const_mul (δ k))).const_mul (w k)
      refine hd.congr_deriv ?_
      ring
    exact HasDerivAt.fun_sum hterm
  have hP_deriv : HasDerivAt (returnProbReal δ w) (2 * (X * X' + Y * Y')) t := by
    unfold returnProbReal
    have hd := (hX.pow 2).add (hY.pow 2)
    refine hd.congr_deriv ?_
    ring
  have hP_nn : 0 ≤ returnProbReal δ w t := by unfold returnProbReal; positivity
  -- Prove `1 - P(t) = ∑_k w_k ((cos(δ_k t) - X)² + (sin(δ_k t) - Y)²) ≥ 0`!
  have h1mP : 1 - returnProbReal δ w t =
      ∑ k : Fin n, w k * ((Real.cos (δ k * t) - X) ^ 2 + (Real.sin (δ k * t) - Y) ^ 2) := by
    have hexp : ∑ k : Fin n, w k * ((Real.cos (δ k * t) - X) ^ 2 + (Real.sin (δ k * t) - Y) ^ 2) =
        (∑ k : Fin n, w k * (Real.cos (δ k * t) ^ 2 + Real.sin (δ k * t) ^ 2)) -
        2 * X * (∑ k : Fin n, w k * Real.cos (δ k * t)) -
        2 * Y * (∑ k : Fin n, w k * Real.sin (δ k * t)) +
        (X ^ 2 + Y ^ 2) * (∑ k : Fin n, w k) := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hexp]
    have htrig : ∑ k : Fin n, w k * (Real.cos (δ k * t) ^ 2 + Real.sin (δ k * t) ^ 2) = 1 := by
      have : ∀ k : Fin n, Real.cos (δ k * t) ^ 2 + Real.sin (δ k * t) ^ 2 = 1 :=
        fun k => Real.cos_sq_add_sin_sq (δ k * t)
      simp_rw [this, mul_one, hsum]
    rw [htrig, hsum]
    unfold returnProbReal
    simp only [X, Y]
    ring
  have hP_le1 : returnProbReal δ w t ≤ 1 := by
    have hnn : 0 ≤ 1 - returnProbReal δ w t := by
      rw [h1mP]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (by positivity)
    linarith
  -- Key Cauchy-Schwarz identity: because `∑ w_k δ_k = 0`, we can subtract `(X, Y)` inside `X', Y'`!
  have hX'_shift : X' = -(∑ k : Fin n, w k * δ k * (Real.sin (δ k * t) - Y)) := by
    have hzero : ∑ k : Fin n, w k * δ k * Y = 0 := by
      rw [← Finset.sum_mul, hmean, zero_mul]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    simp only [X']
    linarith
  have hY'_shift : Y' = ∑ k : Fin n, w k * δ k * (Real.cos (δ k * t) - X) := by
    have hzero : ∑ k : Fin n, w k * δ k * X = 0 := by
      rw [← Finset.sum_mul, hmean, zero_mul]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    simp only [Y']
    linarith
  -- Prove `(X')² + (Y')² ≤ σ² (1 - P(t))` via weighted real Cauchy-Schwarz!
  have hcs_v : X' ^ 2 + Y' ^ 2 ≤ σ ^ 2 * (1 - returnProbReal δ w t) := by
    -- Elementary identity: `X'^2 ≤ (∑ w_k δ_k^2) * (∑ w_k (sin - Y)^2)` and similarly for `Y'^2`!
    have hcs_gen : ∀ (f : Fin n → ℝ),
        (∑ k : Fin n, w k * δ k * f k) ^ 2 ≤
          (∑ k : Fin n, w k * (δ k) ^ 2) * (∑ k : Fin n, w k * (f k) ^ 2) := by
      intro f
      have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
        (f := fun k => Real.sqrt (w k) * δ k) (g := fun k => Real.sqrt (w k) * f k)
      have h1 : ∀ k : Fin n, (Real.sqrt (w k) * δ k) * (Real.sqrt (w k) * f k) = w k * δ k * f k := by
        intro k
        have hsq : Real.sqrt (w k) * Real.sqrt (w k) = w k := by rw [← sq]; exact Real.sq_sqrt (hw k)
        calc (Real.sqrt (w k) * δ k) * (Real.sqrt (w k) * f k)
            = (Real.sqrt (w k) * Real.sqrt (w k)) * δ k * f k := by ring
          _ = w k * δ k * f k := by rw [hsq]
      have h2 : ∀ k : Fin n, (Real.sqrt (w k) * δ k) ^ 2 = w k * (δ k) ^ 2 := by
        intro k; rw [mul_pow, Real.sq_sqrt (hw k)]
      have h3 : ∀ k : Fin n, (Real.sqrt (w k) * f k) ^ 2 = w k * (f k) ^ 2 := by
        intro k; rw [mul_pow, Real.sq_sqrt (hw k)]
      simp_rw [h1, h2, h3] at h
      exact h
    have hcs1 := hcs_gen (fun k => Real.sin (δ k * t) - Y)
    have hcs2 := hcs_gen (fun k => Real.cos (δ k * t) - X)
    rw [hvar] at hcs1 hcs2
    have hX2 : X' ^ 2 ≤ σ ^ 2 * ∑ k : Fin n, w k * (Real.sin (δ k * t) - Y) ^ 2 := by
      rw [hX'_shift, neg_sq]; exact hcs1
    have hY2 : Y' ^ 2 ≤ σ ^ 2 * ∑ k : Fin n, w k * (Real.cos (δ k * t) - X) ^ 2 := by
      rw [hY'_shift]; exact hcs2
    have hcomb : ∑ k : Fin n, w k * (Real.cos (δ k * t) - X) ^ 2 +
        ∑ k : Fin n, w k * (Real.sin (δ k * t) - Y) ^ 2 = 1 - returnProbReal δ w t := by
      rw [h1mP, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    nlinarith
  -- Finally `(2(X X' + Y Y'))² ≤ 4 (X² + Y²)(X'² + Y'²) ≤ 4 P(t) σ² (1 - P(t))`!
  have hlag : (X * X' + Y * Y') ^ 2 ≤ (X ^ 2 + Y ^ 2) * (X' ^ 2 + Y' ^ 2) := by
    nlinarith [sq_nonneg (X * Y' - Y * X')]
  have hfinal : (2 * (X * X' + Y * Y')) ^ 2 ≤
      4 * σ ^ 2 * returnProbReal δ w t * (1 - returnProbReal δ w t) := by
    have hPdef : returnProbReal δ w t = X ^ 2 + Y ^ 2 := rfl
    rw [hPdef] at hcs_v ⊢
    have hXY_nn : 0 ≤ X ^ 2 + Y ^ 2 := by positivity
    nlinarith
  exact ⟨hP_deriv, hP_nn, hP_le1, hfinal⟩

/-- **Theorem 10A (Universal Mandelstam-Tamm / QGTL Speed Limit for Early State Exclusion)**:
For ANY quantum system with discrete eigenvalues `lam`, probability weights `w` (`w k ≥ 0`,
`∑ w k = 1`), mean energy `μ = ∑ w k * lam k`, and energy standard deviation `σ > 0`
(`∑ w k * (lam k - μ)² = σ²`), EVERY time `τ > 0` at which `returnAmpComplex lam w τ = 0`
satisfies `π / (2 * σ) ≤ τ`! -/
theorem mandelstam_tamm_ese_bound {n : ℕ} (lam w : Fin n → ℝ) (μ σ τ : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k : Fin n, w k = 1)
    (hmean : ∑ k : Fin n, w k * lam k = μ)
    (hvar : ∑ k : Fin n, w k * (lam k - μ) ^ 2 = σ ^ 2)
    (hσ : 0 < σ) (hτ : 0 < τ) (hzero : returnAmpComplex lam w τ = 0) :
    Real.pi / (2 * σ) ≤ τ := by
  let δ : Fin n → ℝ := fun k => lam k - μ
  let P : ℝ → ℝ := returnProbReal δ w
  have hδ_mean : ∑ k : Fin n, w k * δ k = 0 := by
    have : ∑ k : Fin n, w k * (lam k - μ) = (∑ k : Fin n, w k * lam k) - μ * (∑ k : Fin n, w k) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [this, hmean, hsum]; ring
  have hP0 : P 0 = 1 := by
    simp [P, returnProbReal, hsum]
  have hPτ : P τ = 0 := by
    have h := normSq_returnAmpComplex_eq_returnProbReal lam w μ τ
    rw [hzero, map_zero] at h
    exact h.symm
  have hP_cont : Continuous P := by unfold P returnProbReal; fun_prop
  -- Isolate the open crossing interval `(t1, t2) ⊆ [0, τ]` where `P(t1) = 1`, `P(t2) = 0`,
  -- and `0 < P(t) < 1` strictly for EVERY `t ∈ (t1, t2)`!
  let S0 : Set ℝ := {t ∈ Set.Icc (0 : ℝ) τ | P t = 0}
  have hS0_ne : S0.Nonempty := ⟨τ, ⟨hτ.le, le_rfl⟩, hPτ⟩
  have hS0_closed : IsClosed S0 :=
    isClosed_Icc.inter (isClosed_eq hP_cont continuous_const)
  have hS0_bdd : BddBelow S0 := ⟨0, fun _ ht => ht.1.1⟩
  set t2 : ℝ := sInf S0
  have ht2_mem : t2 ∈ S0 := hS0_closed.csInf_mem hS0_ne hS0_bdd
  have ht2_pos : 0 < t2 := by
    rcases eq_or_lt_of_le ht2_mem.1.1 with h0 | hp
    · rw [← h0] at ht2_mem; linarith [hP0, ht2_mem.2]
    · exact hp
  have ht2_le_τ : t2 ≤ τ := ht2_mem.1.2
  let S1 : Set ℝ := {t ∈ Set.Icc (0 : ℝ) t2 | P t = 1}
  have hS1_ne : S1.Nonempty := ⟨0, ⟨le_rfl, ht2_pos.le⟩, hP0⟩
  have hS1_closed : IsClosed S1 :=
    isClosed_Icc.inter (isClosed_eq hP_cont continuous_const)
  have hS1_bdd : BddAbove S1 := ⟨t2, fun _ ht => ht.1.2⟩
  set t1 : ℝ := sSup S1
  have ht1_mem : t1 ∈ S1 := hS1_closed.csSup_mem hS1_ne hS1_bdd
  have ht1_lt_t2 : t1 < t2 := by
    rcases eq_or_lt_of_le ht1_mem.1.2 with heq | hlt
    · rw [heq] at ht1_mem; linarith [ht1_mem.2, ht2_mem.2]
    · exact hlt
  have hP_interior : ∀ t ∈ Set.Ioo t1 t2, 0 < P t ∧ P t < 1 := by
    intro t ht
    have hbounds := returnProbReal_deriv_sq_le δ w σ hw hsum hδ_mean hvar t
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hbounds.2.1 with h0 | hp
      · exfalso
        have hmem0 : t ∈ S0 := ⟨⟨le_trans ht1_mem.1.1 ht.1.le, le_trans ht.2.le ht2_le_τ⟩, h0.symm⟩
        have hle := csInf_le hS0_bdd hmem0
        linarith [ht.2]
      · exact hp
    · rcases eq_or_lt_of_le hbounds.2.2.1 with h1 | hlt
      · exfalso
        have hmem1 : t ∈ S1 := ⟨⟨le_trans ht1_mem.1.1 ht.1.le, ht.2.le⟩, h1⟩
        have hge := le_csSup hS1_bdd hmem1
        linarith [ht.1]
      · exact hlt
  -- Apply Mean Value Theorem to `h(t) = arccos(2 P(t) - 1)` on `[t1, t2]`!
  let h : ℝ → ℝ := fun t => Real.arccos (2 * P t - 1)
  have hh_cont : ContinuousOn h (Set.Icc t1 t2) :=
    (Real.continuous_arccos.comp ((continuous_const.mul hP_cont).sub continuous_const)).continuousOn
  have hh_deriv : ∀ t ∈ Set.Ioo t1 t2,
      ∃ d : ℝ, HasDerivAt h d t ∧ d ≤ 2 * σ := by
    intro t ht
    have ⟨hP_pos, hP_lt1⟩ := hP_interior t ht
    have hinfo := returnProbReal_deriv_sq_le δ w σ hw hsum hδ_mean hvar t
    let dP : ℝ := 2 * ((∑ k : Fin n, w k * Real.cos (δ k * t)) *
        -(∑ k : Fin n, w k * δ k * Real.sin (δ k * t)) +
      (∑ k : Fin n, w k * Real.sin (δ k * t)) *
        (∑ k : Fin n, w k * δ k * Real.cos (δ k * t)))
    have hPd : HasDerivAt P dP t := hinfo.1
    have harg_d : HasDerivAt (fun s => 2 * P s - 1) (2 * dP) t :=
      (hPd.const_mul 2).sub_const 1
    have hne1 : 2 * P t - 1 ≠ -1 := by linarith
    have hne2 : 2 * P t - 1 ≠ 1 := by linarith
    have harc := (Real.hasDerivAt_arccos hne1 hne2).comp t harg_d
    refine ⟨-(1 / Real.sqrt (1 - (2 * P t - 1) ^ 2)) * (2 * dP), harc, ?_⟩
    have hrad : 1 - (2 * P t - 1) ^ 2 = 4 * (P t * (1 - P t)) := by ring
    have hrad_pos : 0 < P t * (1 - P t) := mul_pos hP_pos (sub_pos.mpr hP_lt1)
    have hsqrt_eq : Real.sqrt (1 - (2 * P t - 1) ^ 2) = 2 * Real.sqrt (P t * (1 - P t)) := by
      rw [hrad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [hsqrt_eq]
    have hs_pos : 0 < Real.sqrt (P t * (1 - P t)) := Real.sqrt_pos.mpr hrad_pos
    have hsimp : -(1 / (2 * Real.sqrt (P t * (1 - P t)))) * (2 * dP) =
        -dP / Real.sqrt (P t * (1 - P t)) := by
      field_simp [hs_pos.ne']
    rw [hsimp, div_le_iff₀ hs_pos]
    -- Need `-dP ≤ 2 * σ * √(P(t)(1 - P(t)))`, which follows from `dP² ≤ 4 σ² P(t)(1 - P(t))`!
    have hsq : (-dP) ^ 2 ≤ (2 * σ * Real.sqrt (P t * (1 - P t))) ^ 2 := by
      rw [neg_sq, mul_pow, mul_pow, Real.sq_sqrt hrad_pos.le]
      have h4 := hinfo.2.2.2
      linarith
    have hrhs_nn : 0 ≤ 2 * σ * Real.sqrt (P t * (1 - P t)) := by positivity
    nlinarith
  have hmvt := exists_deriv_eq_slope h ht1_lt_t2 hh_cont fun t ht =>
    let ⟨_, hd, _⟩ := hh_deriv t ht; hd.differentiableAt.differentiableWithinAt
  rcases hmvt with ⟨c, hc, hslope⟩
  rcases hh_deriv c hc with ⟨d, hd, hd_le⟩
  rw [hd.deriv] at hslope
  have hh1 : h t1 = 0 := by simp only [h, ht1_mem.2]; norm_num
  have hh2 : h t2 = Real.pi := by simp only [h, ht2_mem.2]; norm_num
  rw [hh2, hh1, sub_zero] at hslope
  have hpi_le : Real.pi ≤ 2 * σ * (t2 - t1) := by
    have h1 := (div_le_iff₀ (sub_pos.mpr ht1_lt_t2)).mp (by linarith : Real.pi / (t2 - t1) ≤ 2 * σ)
    linarith
  have ht_diff : t2 - t1 ≤ τ := by linarith [ht1_mem.1.1, ht2_le_τ]
  rw [div_le_iff₀ (by positivity : 0 < 2 * σ)]
  nlinarith

/-! ### Part 3: Exact ESE ↔ Early Target Exclusion (ETE) Time-Reversal Duality -/

/-- **Theorem 10B (Exact ESE ↔ ETE Time-Reversal Duality)**:
For ANY persymmetric PST chain of length `n ≥ 1` whose eigenbasis satisfies mirror parity
`u k (n - 1) = (-1)^k * u k 0` and PST phase alignment `e^{-i λ_k T} = η * (-1)^k` with
`‖η‖ = 1` (`Complex.normSq η = 1`), the target-site survival modulus at time `T - t` equals
the initial-site return modulus at time `t` identically for ALL `t ∈ ℝ`!
In particular, `τ ∈ (0, T)` is an Early State Exclusion time if and only if `T - τ` is an
Early Target Exclusion time! -/
theorem ese_ete_duality {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (u : Fin n → Fin n → ℝ)
    (T : ℝ) (η : ℂ) (hη : Complex.normSq η = 1)
    (hparity : ∀ k : Fin n, u k ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ = (-1 : ℝ) ^ (k : ℕ) * u k ⟨0, hn⟩)
    (hpst : ∀ k : Fin n, Complex.exp (-Complex.I * (lam k : ℂ) * (T : ℂ)) = η * (-1 : ℂ) ^ (k : ℕ))
    (t : ℝ) :
    Complex.normSq (targetAmpComplex hn lam u (T - t)) =
      Complex.normSq (returnAmpComplex lam (fun k => (u k ⟨0, hn⟩) ^ 2) t) := by
  have hrel : targetAmpComplex hn lam u (T - t) =
      η * starRingEnd ℂ (returnAmpComplex lam (fun k => (u k ⟨0, hn⟩) ^ 2) t) := by
    unfold targetAmpComplex returnAmpComplex
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hparity k]
    have hexp_split : Complex.exp (-Complex.I * (lam k : ℂ) * ((T - t : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * (lam k : ℂ) * (T : ℂ)) *
        Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hexp_split, hpst k]
    have hconj : starRingEnd ℂ (Complex.exp (-Complex.I * (lam k : ℂ) * (t : ℂ))) =
        Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp
    rw [map_mul, Complex.conj_ofReal, hconj]
    have hsign : ((-1 : ℂ) ^ (k : ℕ)) * ((-1 : ℂ) ^ (k : ℕ)) = 1 := by
      rw [← mul_pow]; norm_num
    push_cast
    calc
      (u k ⟨0, hn⟩ : ℂ) * ((-1 : ℂ) ^ (k : ℕ) * (u k ⟨0, hn⟩ : ℂ)) *
        (η * (-1 : ℂ) ^ (k : ℕ) * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)))
          = η * ((u k ⟨0, hn⟩ : ℂ) ^ 2 *
              (((-1 : ℂ) ^ (k : ℕ)) * ((-1 : ℂ) ^ (k : ℕ))) *
              Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))) := by ring
      _ = η * ((u k ⟨0, hn⟩ : ℂ) ^ 2 * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))) := by
          rw [hsign, mul_one]
  rw [hrel, map_mul, hη, one_mul, Complex.normSq_conj]

end SpectralEclipse
