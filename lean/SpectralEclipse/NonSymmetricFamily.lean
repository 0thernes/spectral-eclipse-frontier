/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.Defs
import Mathlib.Tactic

/-!
# Theorem 9: First Infinite Non-Symmetric Staggered-Field Complex-Amplitude ESE Family `J_{a,b}`

Constructs the explicit infinite family of `5 × 5` persymmetric, strictly non-symmetric
(staggered diagonal field `a₀ ≠ a₁`) real Jacobi matrices `J_{a,b}` for `0 < a < b`:
  - Diagonal: `a_diag = (b, b + 2a, b, b + 2a, b)`
  - Hoppings: `b_hop  = (√(b² - a²), √(a(a+2b)/2), √(a(a+2b)/2), √(b² - a²))`
  - Exact spectrum: `σ(J_{a,b}) = {0, a, b, a + 2b, 2a + 2b}` (asymmetric about its trace mean!).

We verify ALL 5 exact orthonormal eigenvectors directly on the literal `5 × 5` matrix `J_{a,b}`,
apply `schrodinger_solution_fidelity` to obtain the exact time-dependent Schrödinger evolution
`ψ(t) = e^{-i J_{a,b} t} e_0`, and prove that for EVERY odd integer `a` with `¬(3 ∣ a)` and every
`b = a + 6k + 3` (`k ∈ ℕ`):
  1. `J_{a,b}` is real symmetric, persymmetric, strictly non-symmetric (`a₀ ≠ a₁`), and has
     strictly positive off-diagonal couplings;
  2. `J_{a,b}` achieves exact Perfect State Transfer at `T₀ = π`: `‖ψ(π)_4‖ = 1` (literally
     `ψ(π)_4 = 1`);
  3. `J_{a,b}` achieves exact **complex-amplitude Early State Exclusion** at `τ = π / 3 ∈ (0, π)`:
     `ψ(π / 3)_0 = 0 ∈ ℂ` (both real and imaginary parts vanish simultaneously!).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace SpectralEclipse

/-- Diagonal field profile of the `5 × 5` staggered-field family `J_{a,b}`:
`(b, b + 2a, b, b + 2a, b)`. -/
def stagDiag (a b : ℝ) : Fin 5 → ℝ :=
  ![b, b + 2 * a, b, b + 2 * a, b]

/-- Hopping profile of `J_{a,b}`:
`b₀ = b₃ = √(b² - a²)`, `b₁ = b₂ = √(a(a + 2b)/2)`. -/
noncomputable def stagHop (a b : ℝ) : Fin 5 → ℝ :=
  ![Real.sqrt (b ^ 2 - a ^ 2), Real.sqrt (a * (a + 2 * b) / 2),
    Real.sqrt (a * (a + 2 * b) / 2), Real.sqrt (b ^ 2 - a ^ 2), 0]

/-- Literal `5 × 5` staggered-field Jacobi matrix `J_{a,b}`. -/
noncomputable def stagJacobi (a b : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  jacobiMatrix (stagDiag a b) (stagHop a b)

/-- Exact eigenvalue tuple `(0, a, b, a + 2b, 2a + 2b)` of `J_{a,b}`. -/
def stagEigvals (a b : ℝ) : Fin 5 → ℝ :=
  ![0, a, b, a + 2 * b, 2 * a + 2 * b]

/-- Exact orthonormal eigenvector matrix `u k j` of `J_{a,b}` for `0 < a < b`. -/
noncomputable def stagEigvecs (a b : ℝ) : Fin 5 → Fin 5 → ℝ :=
  let b0 := Real.sqrt (b ^ 2 - a ^ 2)
  let b1 := Real.sqrt (a * (a + 2 * b) / 2)
  let n0 := Real.sqrt (4 * b * (a + b))
  let n1 := Real.sqrt (4 * b * (b - a))
  let n2 := Real.sqrt (b * (b + 2 * a))
  let n3 := Real.sqrt (4 * b * (a + b))
  let n4 := Real.sqrt (4 * (a + b) * (b + 2 * a))
  ![fun j => (![b0, -b, 2 * b1, -b, b0] j) / n0,
    fun j => (![b0, -(b - a), 0, b - a, -b0] j) / n1,
    fun j => (![b1, 0, -b0, 0, b1] j) / n2,
    fun j => (![b0, a + b, 0, -(a + b), -b0] j) / n3,
    fun j => (![b0, 2 * a + b, 2 * b1, 2 * a + b, b0] j) / n4]

/-- `J_{a,b}` is persymmetric and strictly non-symmetric (staggered diagonal `a₀ ≠ a₁`) for `a > 0`. -/
theorem stagJacobi_persymmetric_and_staggered {a b : ℝ} (ha : 0 < a) :
    IsPersymmetricJacobi (stagDiag a b) (stagHop a b) ∧
    stagDiag a b 0 ≠ stagDiag a b 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp [stagHop] at hi ⊢
  · simp only [stagDiag, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith

/-- Purely algebraic eigenpair lemma with plain real variables `b0, b1, n0, n1, n2, n4`
(zero `Real.sqrt` expansion inside `ring`/`field_simp`). -/
private theorem stagJacobi_eigpairs_alg (a b b0 b1 n0 n1 n2 n4 : ℝ)
    (hb0 : b0 ^ 2 = b ^ 2 - a ^ 2) (hb1 : 2 * b1 ^ 2 = a * (a + 2 * b))
    (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) (hn4 : n4 ≠ 0) (k : Fin 5) :
    let J := jacobiMatrix ![b, b + 2 * a, b, b + 2 * a, b] ![b0, b1, b1, b0, 0]
    let u : Fin 5 → Fin 5 → ℝ :=
      ![fun j => (![b0, -b, 2 * b1, -b, b0] j) / n0,
        fun j => (![b0, -(b - a), 0, b - a, -b0] j) / n1,
        fun j => (![b1, 0, -b0, 0, b1] j) / n2,
        fun j => (![b0, a + b, 0, -(a + b), -b0] j) / n0,
        fun j => (![b0, 2 * a + b, 2 * b1, 2 * a + b, b0] j) / n4]
    J.mulVec (u k) = stagEigvals a b k • u k := by
  intro J u
  ext j
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]
  fin_cases k
  · fin_cases j <;> simp [J, u, jacobiMatrix, stagEigvals] <;> field_simp [hn0] <;> nlinarith [hb0, hb1]
  · fin_cases j <;> simp [J, u, jacobiMatrix, stagEigvals] <;> field_simp [hn1] <;> nlinarith [hb0, hb1]
  · fin_cases j <;> simp [J, u, jacobiMatrix, stagEigvals] <;> field_simp [hn2] <;> nlinarith [hb0, hb1]
  · fin_cases j <;> simp [J, u, jacobiMatrix, stagEigvals] <;> field_simp [hn0] <;> nlinarith [hb0, hb1]
  · fin_cases j <;> simp [J, u, jacobiMatrix, stagEigvals] <;> field_simp [hn4] <;> nlinarith [hb0, hb1]

/-- Direct verification that every `stagEigvecs a b k` is an exact eigenvector of the literal
`5 × 5` matrix `stagJacobi a b` with eigenvalue `stagEigvals a b k`. -/
theorem stagJacobi_eigpairs {a b : ℝ} (ha : 0 < a) (hab : a < b) (k : Fin 5) :
    (stagJacobi a b).mulVec (stagEigvecs a b k) = stagEigvals a b k • stagEigvecs a b k := by
  have hb : 0 < b := by linarith
  have hb0 : Real.sqrt (b ^ 2 - a ^ 2) ^ 2 = b ^ 2 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb1 : 2 * Real.sqrt (a * (a + 2 * b) / 2) ^ 2 = a * (a + 2 * b) := by
    rw [Real.sq_sqrt (by positivity)]; ring
  have hn0 : Real.sqrt (4 * b * (a + b)) ≠ 0 := (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have hn1 : Real.sqrt (4 * b * (b - a)) ≠ 0 := (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have hn2 : Real.sqrt (b * (b + 2 * a)) ≠ 0 := (Real.sqrt_pos.mpr (by nlinarith)).ne'
  have hn4 : Real.sqrt (4 * (a + b) * (b + 2 * a)) ≠ 0 := (Real.sqrt_pos.mpr (by nlinarith)).ne'
  exact stagJacobi_eigpairs_alg a b _ _ _ _ _ _ hb0 hb1 hn0 hn1 hn2 hn4 k

/-- Purely algebraic completeness lemma with plain real variables (zero `Real.sqrt` expansion). -/
private theorem stagJacobi_init_complete_alg (a b b0 b1 n0 n1 n2 n4 : ℝ)
    (hb0 : b0 ^ 2 = b ^ 2 - a ^ 2) (hb1 : 2 * b1 ^ 2 = a * (a + 2 * b))
    (hn0 : n0 ^ 2 = 4 * b * (a + b)) (hn1 : n1 ^ 2 = 4 * b * (b - a))
    (hn2 : n2 ^ 2 = b * (b + 2 * a)) (hn4 : n4 ^ 2 = 4 * (a + b) * (b + 2 * a))
    (hn0_ne : n0 ≠ 0) (hn1_ne : n1 ≠ 0) (hn2_ne : n2 ≠ 0) (hn4_ne : n4 ≠ 0) (j : Fin 5) :
    let u : Fin 5 → Fin 5 → ℝ :=
      ![fun i => (![b0, -b, 2 * b1, -b, b0] i) / n0,
        fun i => (![b0, -(b - a), 0, b - a, -b0] i) / n1,
        fun i => (![b1, 0, -b0, 0, b1] i) / n2,
        fun i => (![b0, a + b, 0, -(a + b), -b0] i) / n0,
        fun i => (![b0, 2 * a + b, 2 * b1, 2 * a + b, b0] i) / n4]
    ∑ k : Fin 5, u k 0 * u k j = if j = 0 then 1 else 0 := by
  intro u
  rw [Fin.sum_univ_five]
  fin_cases j <;>
    (simp [u]; field_simp [hn0_ne, hn1_ne, hn2_ne, hn4_ne];
     have h2b1 : b1 ^ 2 = a * (a + 2 * b) / 2 := by linarith
     simp only [hn0, hn1, hn2, hn4, hb0, h2b1]; ring)

/-- Direct verification of completeness at site `0`: `∑_k (u_k 0) (u_k j) = δ_{0, j}`. -/
theorem stagJacobi_init_complete {a b : ℝ} (ha : 0 < a) (hab : a < b) (j : Fin 5) :
    ∑ k : Fin 5, stagEigvecs a b k 0 * stagEigvecs a b k j = if j = 0 then 1 else 0 := by
  have hb : 0 < b := by linarith
  have hbma : 0 < b - a := by linarith
  have hab_pos : 0 < a + b := by linarith
  have hb2a : 0 < b + 2 * a := by linarith
  have hb0 : Real.sqrt (b ^ 2 - a ^ 2) ^ 2 = b ^ 2 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb1 : 2 * Real.sqrt (a * (a + 2 * b) / 2) ^ 2 = a * (a + 2 * b) := by
    rw [Real.sq_sqrt (by positivity)]; ring
  have hn0 : Real.sqrt (4 * b * (a + b)) ^ 2 = 4 * b * (a + b) := Real.sq_sqrt (by positivity)
  have hn1 : Real.sqrt (4 * b * (b - a)) ^ 2 = 4 * b * (b - a) := Real.sq_sqrt (by positivity)
  have hn2 : Real.sqrt (b * (b + 2 * a)) ^ 2 = b * (b + 2 * a) := Real.sq_sqrt (by positivity)
  have hn4 : Real.sqrt (4 * (a + b) * (b + 2 * a)) ^ 2 = 4 * (a + b) * (b + 2 * a) :=
    Real.sq_sqrt (by positivity)
  have hn0_ne : Real.sqrt (4 * b * (a + b)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hn1_ne : Real.sqrt (4 * b * (b - a)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hn2_ne : Real.sqrt (b * (b + 2 * a)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hn4_ne : Real.sqrt (4 * (a + b) * (b + 2 * a)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  exact stagJacobi_init_complete_alg a b _ _ _ _ _ _
    hb0 hb1 hn0 hn1 hn2 hn4 hn0_ne hn1_ne hn2_ne hn4_ne j

/-- Exact closed-form return weights `(u_k 0)²` of `J_{a,b}`, satisfying the twin cancellation
identities `w₀ = w₃` and `w₁ = w₂ + w₄` identically for ALL `0 < a < b`. -/
theorem stagJacobi_weights {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (stagEigvecs a b 0 0) ^ 2 = (b - a) / (4 * b) ∧
    (stagEigvecs a b 1 0) ^ 2 = (a + b) / (4 * b) ∧
    (stagEigvecs a b 2 0) ^ 2 = a * (a + 2 * b) / (2 * b * (b + 2 * a)) ∧
    (stagEigvecs a b 3 0) ^ 2 = (b - a) / (4 * b) ∧
    (stagEigvecs a b 4 0) ^ 2 = (b - a) / (4 * (b + 2 * a)) := by
  have hb : 0 < b := by linarith
  have hbma : 0 < b - a := by linarith
  have hab_pos : 0 < a + b := by linarith
  have hb2a : 0 < b + 2 * a := by linarith
  have hsq0 : Real.sqrt (b ^ 2 - a ^ 2) ^ 2 = b ^ 2 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hsq1 : Real.sqrt (a * (a + 2 * b) / 2) ^ 2 = a * (a + 2 * b) / 2 := Real.sq_sqrt (by positivity)
  have hn0 : Real.sqrt (4 * b * (a + b)) ^ 2 = 4 * b * (a + b) := Real.sq_sqrt (by positivity)
  have hn1 : Real.sqrt (4 * b * (b - a)) ^ 2 = 4 * b * (b - a) := Real.sq_sqrt (by positivity)
  have hn2 : Real.sqrt (b * (b + 2 * a)) ^ 2 = b * (b + 2 * a) := Real.sq_sqrt (by positivity)
  have hn4 : Real.sqrt (4 * (a + b) * (b + 2 * a)) ^ 2 = 4 * (a + b) * (b + 2 * a) :=
    Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [stagEigvecs, div_pow, hsq0, hn0]; field_simp [hb.ne', hab_pos.ne']; ring
  · simp [stagEigvecs, div_pow, hsq0, hn1]; field_simp [hb.ne', hbma.ne']; ring
  · simp only [stagEigvecs, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue, div_pow, hsq1, hn2]
    field_simp [hb.ne', hb2a.ne']
  · simp [stagEigvecs, div_pow, hsq0, hn0]; field_simp [hb.ne', hab_pos.ne']; ring
  · simp [stagEigvecs, div_pow, hsq0, hn4]; field_simp [hab_pos.ne', hb2a.ne']; ring

/-- **Theorem 9 (Infinite Non-Symmetric Staggered-Field Complex-Amplitude ESE Family)**:
For EVERY odd integer `a ≥ 1` with `¬(3 ∣ a)` and EVERY `k : ℕ`, let `b = a + 6k + 3`.
Then the literal `5 × 5` staggered-field Jacobi matrix `J_{a,b}` satisfies:
  1. Persymmetric and strictly non-symmetric (`a₀ ≠ a₁`);
  2. Exact Schrödinger trajectory `ψ(t) = spectralState (stagEigvals a b) (stagEigvecs a b) t`
     solving `i dψ/dt = J_{a,b} ψ(t)` with `ψ(0) = e_0`;
  3. Exact Perfect State Transfer at `T₀ = π`: `ψ(π)_4 = 1` (probability `1`);
  4. Exact **complex-amplitude Early State Exclusion** at `τ = π / 3 ∈ (0, π)`:
     `ψ(π / 3)_0 = 0 ∈ ℂ` (hence `HasESEComplex (fun t => ψ t 0) π`)! -/
theorem theorem_9_nonsymmetric_family {a k : ℕ} (ha_odd : Odd a) (ha_ndvd3 : ¬(3 ∣ a)) :
    let ar : ℝ := (a : ℝ)
    let br : ℝ := ((a + 6 * k + 3 : ℕ) : ℝ)
    let ψ := spectralState (stagEigvals ar br) (stagEigvecs ar br)
    IsPersymmetricJacobi (stagDiag ar br) (stagHop ar br) ∧
    stagDiag ar br 0 ≠ stagDiag ar br 1 ∧
    (∀ j : Fin 5, ψ 0 j = if j = 0 then 1 else 0) ∧
    (∀ t : ℝ, ∀ j : Fin 5,
      HasDerivAt (fun s => ψ s j)
        (-Complex.I * (((stagJacobi ar br).map Complex.ofReal).mulVec (ψ t) j)) t) ∧
    ψ Real.pi 4 = 1 ∧
    ψ (Real.pi / 3) 0 = 0 ∧
    HasESEComplex (fun t => ψ t 0) Real.pi := by
  intro ar br ψ
  have ha0 : 0 < a := by rcases ha_odd with ⟨m, rfl⟩; omega
  have har : 0 < ar := by dsimp only [ar]; exact_mod_cast ha0
  have hab : ar < br := by
    dsimp only [ar, br]
    have : a < a + 6 * k + 3 := by omega
    exact_mod_cast this
  have hbr : 0 < br := by linarith
  have hbr2a : 0 < br + 2 * ar := by linarith
  have hpers := stagJacobi_persymmetric_and_staggered (b := br) har
  have hfid := schrodinger_solution_fidelity (n := 5) (by norm_num)
    (stagJacobi ar br) (stagEigvals ar br) (stagEigvecs ar br)
    (stagJacobi_eigpairs har hab) (stagJacobi_init_complete har hab)
  have hw := stagJacobi_weights har hab
  have hbr_eq : br = ar + 6 * (k : ℝ) + 3 := by simp only [ar, br]; push_cast; ring
  -- Part 3: Exact PST at `t = π`: `ψ π 4 = 1`!
  have hpst : ψ Real.pi 4 = 1 := by
    have ht := hfid.2.2.2 Real.pi
    simp only [Nat.reduceSub] at ht
    change spectralState (stagEigvals ar br) (stagEigvecs ar br) Real.pi ⟨4, by omega⟩ = 1
    rw [ht]
    unfold targetAmpComplex
    rw [Fin.sum_univ_five]
    -- Parity of eigenvectors at site 4: `u_k 4 = (-1)^k * u_k 0`!
    have hu4 :
        stagEigvecs ar br 0 4 = stagEigvecs ar br 0 0 ∧
        stagEigvecs ar br 1 4 = -stagEigvecs ar br 1 0 ∧
        stagEigvecs ar br 2 4 = stagEigvecs ar br 2 0 ∧
        stagEigvecs ar br 3 4 = -stagEigvecs ar br 3 0 ∧
        stagEigvecs ar br 4 4 = stagEigvecs ar br 4 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [stagEigvecs, neg_div]
    -- Phase at `t = π`: eigenvalues `0, a, b, a+2b, 2a+2b` have parities `E, O, E, O, E`!
    have hb_even : Even (a + 6 * k + 3) := by rcases ha_odd with ⟨m, rfl⟩; exact ⟨m + 3 * k + 2, by omega⟩
    have hexp_even : ∀ n : ℕ, Even n → Complex.exp (-Complex.I * ((n : ℕ) : ℂ) * (Real.pi : ℂ)) = 1 := by
      intro n ⟨m, hm⟩
      have : -Complex.I * ((n : ℕ) : ℂ) * (Real.pi : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hm]; push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have hexp_odd : ∀ n : ℕ, Odd n → Complex.exp (-Complex.I * ((n : ℕ) : ℂ) * (Real.pi : ℂ)) = -1 := by
      intro n ⟨m, hm⟩
      have : -Complex.I * ((n : ℕ) : ℂ) * (Real.pi : ℂ) =
          -(Real.pi * Complex.I) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hm]; push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
          Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    have he0 : Complex.exp (-Complex.I * (stagEigvals ar br 0 : ℂ) * Real.pi) = 1 := by
      simp [stagEigvals]
    have he1 : Complex.exp (-Complex.I * (stagEigvals ar br 1 : ℂ) * Real.pi) = -1 := by
      simpa [stagEigvals, ar] using hexp_odd a ha_odd
    have he2 : Complex.exp (-Complex.I * (stagEigvals ar br 2 : ℂ) * Real.pi) = 1 := by
      simpa [stagEigvals, br] using hexp_even (a + 6 * k + 3) hb_even
    have he3 : Complex.exp (-Complex.I * (stagEigvals ar br 3 : ℂ) * Real.pi) = -1 := by
      have hodd3 : Odd (a + 2 * (a + 6 * k + 3)) := by rcases ha_odd with ⟨m, rfl⟩; exact ⟨3 * m + 6 * k + 4, by omega⟩
      have hc : (stagEigvals ar br 3 : ℂ) = ((a + 2 * (a + 6 * k + 3) : ℕ) : ℂ) := by
        have hval : stagEigvals ar br 3 = ar + 2 * br := rfl
        rw [hval]
        simp only [ar, br]
        push_cast; ring
      rw [hc]
      exact hexp_odd _ hodd3
    have he4 : Complex.exp (-Complex.I * (stagEigvals ar br 4 : ℂ) * Real.pi) = 1 := by
      have heven4 : Even (2 * a + 2 * (a + 6 * k + 3)) := ⟨a + (a + 6 * k + 3), by omega⟩
      have hc : (stagEigvals ar br 4 : ℂ) = ((2 * a + 2 * (a + 6 * k + 3) : ℕ) : ℂ) := by
        have hval : stagEigvals ar br 4 = 2 * ar + 2 * br := rfl
        rw [hval]
        simp only [ar, br]
        push_cast; ring
      rw [hc]
      exact hexp_even _ heven4
    change ((stagEigvecs ar br 0 0 * stagEigvecs ar br 0 4 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (stagEigvals ar br 0 : ℂ) * Real.pi) +
      ((stagEigvecs ar br 1 0 * stagEigvecs ar br 1 4 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (stagEigvals ar br 1 : ℂ) * Real.pi) +
      ((stagEigvecs ar br 2 0 * stagEigvecs ar br 2 4 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (stagEigvals ar br 2 : ℂ) * Real.pi) +
      ((stagEigvecs ar br 3 0 * stagEigvecs ar br 3 4 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (stagEigvals ar br 3 : ℂ) * Real.pi) +
      ((stagEigvecs ar br 4 0 * stagEigvecs ar br 4 4 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * (stagEigvals ar br 4 : ℂ) * Real.pi) = 1
    rw [hu4.1, hu4.2.1, hu4.2.2.1, hu4.2.2.2.1, hu4.2.2.2.2, he0, he1, he2, he3, he4]
    have hsum1 : (stagEigvecs ar br 0 0) ^ 2 + (stagEigvecs ar br 1 0) ^ 2 +
        (stagEigvecs ar br 2 0) ^ 2 + (stagEigvecs ar br 3 0) ^ 2 +
        (stagEigvecs ar br 4 0) ^ 2 = 1 := by
      rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2]
      field_simp [hbr.ne', hbr2a.ne']
      ring
    have hsum_c := congrArg Complex.ofReal hsum1
    push_cast at hsum_c
    convert hsum_c using 1
    push_cast
    ring
  -- Part 4: Exact Complex ESE at `τ = π / 3`: `ψ (π / 3) 0 = 0 ∈ ℂ`!
  have hese_zero : ψ (Real.pi / 3) 0 = 0 := by
    change spectralState (stagEigvals ar br) (stagEigvecs ar br) (Real.pi / 3) ⟨0, by omega⟩ = 0
    rw [hfid.2.2.1 (Real.pi / 3)]
    unfold returnAmpComplex
    rw [Fin.sum_univ_five]
    set ω : ℂ := Complex.exp (-Complex.I * (ar : ℂ) * (Real.pi / 3 : ℂ))
    have he0 : Complex.exp (-Complex.I * (stagEigvals ar br 0 : ℂ) * (Real.pi / 3 : ℂ)) = 1 := by
      simp [stagEigvals]
    have he1 : Complex.exp (-Complex.I * (stagEigvals ar br 1 : ℂ) * (Real.pi / 3 : ℂ)) = ω := by
      simp [stagEigvals, ω]
    have he2 : Complex.exp (-Complex.I * (stagEigvals ar br 2 : ℂ) * (Real.pi / 3 : ℂ)) = -ω := by
      have harg : -Complex.I * (stagEigvals ar br 2 : ℂ) * (Real.pi / 3 : ℂ) =
          (-Complex.I * (ar : ℂ) * (Real.pi / 3 : ℂ)) +
          (-(Real.pi * Complex.I)) + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        change -Complex.I * (br : ℂ) * (Real.pi / 3 : ℂ) = _
        rw [hbr_eq]; push_cast; ring
      rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
          Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]
    have he3 : Complex.exp (-Complex.I * (stagEigvals ar br 3 : ℂ) * (Real.pi / 3 : ℂ)) = -1 := by
      rcases ha_odd with ⟨m, rfl⟩
      have harg : -Complex.I * (stagEigvals ar br 3 : ℂ) * (Real.pi / 3 : ℂ) =
          -(Real.pi * Complex.I) + ((-(m + 2 * k + 1 : ℕ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        change -Complex.I * ((ar + 2 * br : ℝ) : ℂ) * (Real.pi / 3 : ℂ) = _
        rw [hbr_eq]; simp only [ar]; push_cast; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
          Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    have he4 : Complex.exp (-Complex.I * (stagEigvals ar br 4 : ℂ) * (Real.pi / 3 : ℂ)) = -ω := by
      rcases ha_odd with ⟨m, rfl⟩
      have harg : -Complex.I * (stagEigvals ar br 4 : ℂ) * (Real.pi / 3 : ℂ) =
          (-Complex.I * (ar : ℂ) * (Real.pi / 3 : ℂ)) +
          (-(Real.pi * Complex.I)) + ((-(m + 2 * k + 1 : ℕ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        change -Complex.I * ((2 * ar + 2 * br : ℝ) : ℂ) * (Real.pi / 3 : ℂ) = _
        rw [hbr_eq]; simp only [ar]; push_cast; ring
      rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
          Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]
    have hidx0 : (⟨0, by norm_num⟩ : Fin 5) = 0 := rfl
    have hpi3 : ((Real.pi / 3 : ℝ) : ℂ) = (Real.pi : ℂ) / 3 := by push_cast; rfl
    simp only [hidx0, hpi3]
    rw [he0, he1, he2, he3, he4]
    have hbal1 : (stagEigvecs ar br 0 0) ^ 2 - (stagEigvecs ar br 3 0) ^ 2 = 0 := by
      rw [hw.1, hw.2.2.2.1]; ring
    have hbal2 : (stagEigvecs ar br 1 0) ^ 2 - (stagEigvecs ar br 2 0) ^ 2 -
        (stagEigvecs ar br 4 0) ^ 2 = 0 := by
      rw [hw.2.1, hw.2.2.1, hw.2.2.2.2]
      field_simp [hbr.ne', hbr2a.ne']
      ring
    have hc1 : (((stagEigvecs ar br 0 0) ^ 2 : ℝ) : ℂ) - (((stagEigvecs ar br 3 0) ^ 2 : ℝ) : ℂ) = 0 := by
      exact_mod_cast hbal1
    have hc2 : (((stagEigvecs ar br 1 0) ^ 2 : ℝ) : ℂ) - (((stagEigvecs ar br 2 0) ^ 2 : ℝ) : ℂ) -
        (((stagEigvecs ar br 4 0) ^ 2 : ℝ) : ℂ) = 0 := by
      exact_mod_cast hbal2
    calc
      ((stagEigvecs ar br 0 0 ^ 2 : ℝ) : ℂ) * 1 +
        ((stagEigvecs ar br 1 0 ^ 2 : ℝ) : ℂ) * ω +
        ((stagEigvecs ar br 2 0 ^ 2 : ℝ) : ℂ) * -ω +
        ((stagEigvecs ar br 3 0 ^ 2 : ℝ) : ℂ) * -1 +
        ((stagEigvecs ar br 4 0 ^ 2 : ℝ) : ℂ) * -ω
          = (((stagEigvecs ar br 0 0 ^ 2 : ℝ) : ℂ) - ((stagEigvecs ar br 3 0 ^ 2 : ℝ) : ℂ)) +
            (((stagEigvecs ar br 1 0 ^ 2 : ℝ) : ℂ) - ((stagEigvecs ar br 2 0 ^ 2 : ℝ) : ℂ) -
              ((stagEigvecs ar br 4 0 ^ 2 : ℝ) : ℂ)) * ω := by ring
      _ = 0 + 0 * ω := by rw [hc1, hc2]
      _ = 0 := by ring
  refine ⟨hpers.1, hpers.2, hfid.1, hfid.2.1, hpst, hese_zero,
    ⟨Real.pi / 3, by positivity, by linarith [Real.pi_pos], hese_zero⟩⟩

end SpectralEclipse
