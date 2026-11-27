/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Isolated Mathlib-Only Challenge Specification (Spectral Eclipse Frontier, Theorems 1–10)

This file imports ONLY Mathlib (ZERO imports from our proof library `SpectralEclipse`).
It defines the literal `n × n` real symmetric Jacobi matrix `jacobiMatrix`, persymmetry,
Schrödinger spectral state `spectralState`, complex return/target amplitudes, the Hochstadt
return amplitudes `amp4`–`amp11`, the universal cluster-to-core ratio `clusterToCoreRatio`,
and the non-symmetric staggered-field family `stagJacobi`, and states all 12 headline
comparator targets covering Theorems 1–10 of the Spectral Eclipse Frontier program
(including Conjecture 4.1 of Escobar-Garcia-Minenkova, arXiv:2507.18767v1).

NOTE: Every `sorry` in this file is intentional — `Challenge.lean` is the isolated statement
specification checked against sorry-free `Solution.lean` by
`lake comparator --config comparator.json --paranoid`.
-/

@[expose] public section

open scoped BigOperators
open Real Filter Topology Finset

namespace SpectralEclipse.ComparatorTarget

/-- Literal `n × n` real symmetric tridiagonal Jacobi matrix. -/
def jacobiMatrix {n : ℕ} (a b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then a i
    else if (i : ℕ) + 1 = (j : ℕ) then b i
    else if (j : ℕ) + 1 = (i : ℕ) then b j
    else 0

/-- Persymmetry (mirror symmetry about the anti-diagonal) of a Jacobi matrix `(a, b)`. -/
def IsPersymmetricJacobi {n : ℕ} (a b : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, a (Fin.rev i) = a i) ∧
  (∀ i : Fin n, (hi : (i : ℕ) + 1 < n) →
    b ⟨n - 2 - (i : ℕ), by omega⟩ = b i)

/-- Spectral state vector `ψ(t) = ∑_k (u_k 0) e^{-i λ_k t} u_k ∈ ℂ^n`. -/
noncomputable def spectralState {n : ℕ} (lam : Fin n → ℝ) (u : Fin n → Fin n → ℝ)
    (t : ℝ) : Fin n → ℂ :=
  fun j => ∑ k : Fin n,
    ((u k ⟨0, Nat.pos_of_ne_zero (by
        intro h0; subst h0; exact Fin.elim0 j)⟩ : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (lam k : ℂ) * (t : ℂ)) * (u k j : ℂ)

/-- Return amplitude `⟨e^{-iJt} e_0, e_0⟩ = ∑_k w_k e^{-i λ_k t}` in `ℂ`. -/
noncomputable def returnAmpComplex {n : ℕ} (lam w : Fin n → ℝ) (t : ℝ) : ℂ :=
  ∑ k : Fin n, (w k : ℂ) * Complex.exp (-Complex.I * (lam k : ℂ) * (t : ℂ))

/-- Target transfer amplitude `⟨e^{-iJt} e_0, e_{n-1}⟩` for a chain of length `n ≥ 1`. -/
noncomputable def targetAmpComplex {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ)
    (u : Fin n → Fin n → ℝ) (t : ℝ) : ℂ :=
  ∑ k : Fin n,
    ((u k ⟨0, hn⟩ * u k ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (lam k : ℂ) * (t : ℂ))

/-- Early State Exclusion (ESE) predicate for a real-valued return amplitude on `(0, π)`. -/
def HasESEReal (A : ℝ → ℝ) : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi ∧ A τ = 0

/-- Early State Exclusion (ESE) predicate for a complex-valued return amplitude on `(0, T)`. -/
def HasESEComplex (A : ℝ → ℂ) (T : ℝ) : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ τ < T ∧ A τ = 0

/-- Normalized return amplitude for `4 × 4` symmetric PST chain `{±p/2, ±q/2}`. -/
noncomputable def amp4 (p q t : ℝ) : ℝ :=
  (q * Real.cos (p * t / 2) + p * Real.cos (q * t / 2)) / (p + q)

/-- Normalized return amplitude for `5 × 5` symmetric PST chain `{0, ±y, ±x}`. -/
noncomputable def amp5 (y x t : ℝ) : ℝ :=
  let w0 := 1 / (y ^ 2 * x ^ 2)
  let w1 := 1 / (y ^ 2 * (x ^ 2 - y ^ 2))
  let w2 := 1 / (x ^ 2 * (x ^ 2 - y ^ 2))
  (w0 + w1 * Real.cos (y * t) + w2 * Real.cos (x * t)) / (w0 + w1 + w2)

/-- Normalized return amplitude for `6 × 6` symmetric PST chain `{±p/2, ±q/2, ±r/2}`. -/
noncomputable def amp6 (p q r t : ℝ) : ℝ :=
  let w1 := 1 / (p * (q ^ 2 - p ^ 2) * (r ^ 2 - p ^ 2))
  let w2 := 1 / (q * (q ^ 2 - p ^ 2) * (r ^ 2 - q ^ 2))
  let w3 := 1 / (r * (r ^ 2 - p ^ 2) * (r ^ 2 - q ^ 2))
  (w1 * Real.cos (p * t / 2) + w2 * Real.cos (q * t / 2) + w3 * Real.cos (r * t / 2)) /
    (w1 + w2 + w3)

/-- Normalized return amplitude for `7 × 7` symmetric PST chain `{0, ±x, ±y, ±z}`. -/
noncomputable def amp7 (x y z t : ℝ) : ℝ :=
  let w0 := 1 / (x ^ 2 * y ^ 2 * z ^ 2)
  let w1 := 1 / (x ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - x ^ 2))
  let w2 := 1 / (y ^ 2 * (y ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2))
  let w3 := 1 / (z ^ 2 * (z ^ 2 - x ^ 2) * (z ^ 2 - y ^ 2))
  (w0 + w1 * Real.cos (x * t) + w2 * Real.cos (y * t) + w3 * Real.cos (z * t)) /
    (w0 + w1 + w2 + w3)

/-- Normalized return amplitude for `8 × 8` symmetric PST chain `{±p₁/2, ±p₂/2, ±p₃/2, ±p₄/2}`. -/
noncomputable def amp8 (p1 p2 p3 p4 t : ℝ) : ℝ :=
  let w1 := 1 / (p1 * (p2 ^ 2 - p1 ^ 2) * (p3 ^ 2 - p1 ^ 2) * (p4 ^ 2 - p1 ^ 2))
  let w2 := 1 / (p2 * (p2 ^ 2 - p1 ^ 2) * (p3 ^ 2 - p2 ^ 2) * (p4 ^ 2 - p2 ^ 2))
  let w3 := 1 / (p3 * (p3 ^ 2 - p1 ^ 2) * (p3 ^ 2 - p2 ^ 2) * (p4 ^ 2 - p3 ^ 2))
  let w4 := 1 / (p4 * (p4 ^ 2 - p1 ^ 2) * (p4 ^ 2 - p2 ^ 2) * (p4 ^ 2 - p3 ^ 2))
  (w1 * Real.cos (p1 * t / 2) + w2 * Real.cos (p2 * t / 2) +
    w3 * Real.cos (p3 * t / 2) + w4 * Real.cos (p4 * t / 2)) / (w1 + w2 + w3 + w4)

/-- Normalized return amplitude for `9 × 9` symmetric PST chain `{0, ±a, ±b, ±c, ±d}`. -/
noncomputable def amp9 (a b c d t : ℝ) : ℝ :=
  let w0 := 1 / (a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2)
  let w1 := 1 / (a ^ 2 * (b ^ 2 - a ^ 2) * (c ^ 2 - a ^ 2) * (d ^ 2 - a ^ 2))
  let w2 := 1 / (b ^ 2 * (b ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - b ^ 2))
  let w3 := 1 / (c ^ 2 * (c ^ 2 - a ^ 2) * (c ^ 2 - b ^ 2) * (d ^ 2 - c ^ 2))
  let w4 := 1 / (d ^ 2 * (d ^ 2 - a ^ 2) * (d ^ 2 - b ^ 2) * (d ^ 2 - c ^ 2))
  (w0 + w1 * Real.cos (a * t) + w2 * Real.cos (b * t) +
    w3 * Real.cos (c * t) + w4 * Real.cos (d * t)) / (w0 + w1 + w2 + w3 + w4)

/-- Normalized return amplitude for `11 × 11` symmetric PST chain `{0, ±l₁, ±l₂, ±l₃, ±l₄, ±l₅}`. -/
noncomputable def amp11 (l1 l2 l3 l4 l5 t : ℝ) : ℝ :=
  let w0 := 1 / (l1 ^ 2 * l2 ^ 2 * l3 ^ 2 * l4 ^ 2 * l5 ^ 2)
  let w1 := 1 / (l1 ^ 2 * (l2 ^ 2 - l1 ^ 2) * (l3 ^ 2 - l1 ^ 2) * (l4 ^ 2 - l1 ^ 2) * (l5 ^ 2 - l1 ^ 2))
  let w2 := 1 / (l2 ^ 2 * (l2 ^ 2 - l1 ^ 2) * (l3 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l2 ^ 2) * (l5 ^ 2 - l2 ^ 2))
  let w3 := 1 / (l3 ^ 2 * (l3 ^ 2 - l1 ^ 2) * (l3 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l3 ^ 2))
  let w4 := 1 / (l4 ^ 2 * (l4 ^ 2 - l1 ^ 2) * (l4 ^ 2 - l2 ^ 2) * (l4 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l4 ^ 2))
  let w5 := 1 / (l5 ^ 2 * (l5 ^ 2 - l1 ^ 2) * (l5 ^ 2 - l2 ^ 2) * (l5 ^ 2 - l3 ^ 2) * (l5 ^ 2 - l4 ^ 2))
  (w0 + w1 * Real.cos (l1 * t) + w2 * Real.cos (l2 * t) + w3 * Real.cos (l3 * t) +
    w4 * Real.cos (l4 * t) + w5 * Real.cos (l5 * t)) / (w0 + w1 + w2 + w3 + w4 + w5)

/-- Leading cluster-to-core Hochstadt weight ratio `Φ(R, r, M)` for `(R, r)` phase transition. -/
noncomputable def clusterToCoreRatio (R r : ℕ) (M : ℝ) : ℝ :=
  (((R - 1).factorial : ℝ) / (((r - 1).factorial : ℝ) * (2 : ℝ) ^ (R - 1))) *
    M ^ ((r : ℤ) - (R : ℤ))

/-- Diagonal field profile of the `5 × 5` staggered-field family `J_{a,b}`. -/
def stagDiag (a b : ℝ) : Fin 5 → ℝ :=
  ![b, b + 2 * a, b, b + 2 * a, b]

/-- Hopping profile of `J_{a,b}`. -/
noncomputable def stagHop (a b : ℝ) : Fin 5 → ℝ :=
  ![Real.sqrt (b ^ 2 - a ^ 2), Real.sqrt (a * (a + 2 * b) / 2),
    Real.sqrt (a * (a + 2 * b) / 2), Real.sqrt (b ^ 2 - a ^ 2), 0]

/-- Literal `5 × 5` staggered-field Jacobi matrix `J_{a,b}`. -/
noncomputable def stagJacobi (a b : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  jacobiMatrix (stagDiag a b) (stagHop a b)

/-- Exact eigenvalue tuple `(0, a, b, a + 2b, 2a + 2b)` of `J_{a,b}`. -/
def stagEigvals (a b : ℝ) : Fin 5 → ℝ :=
  ![0, a, b, a + 2 * b, 2 * a + 2 * b]

/-- Exact orthonormal eigenvector matrix of `J_{a,b}`. -/
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

/-- Target 1 (Theorem 1): Complete `4 × 4` symmetric PST dichotomy. -/
theorem target_theorem_1_4x4 {p q : ℕ} (hp_odd : Odd p) (hq_odd : Odd q) (hpq : p < q)
    (hgap : (q - p) % 4 = 2) :
    ¬HasESEReal (amp4 (p : ℝ) (q : ℝ)) ↔ p = 1 := by
  sorry

/-- Target 2 (Theorem 2): Complete `5 × 5` symmetric PST dichotomy. -/
theorem target_theorem_2_5x5 {y x : ℕ} (hy_odd : Odd y) (hx_even : Even x)
    (hyx : y < x) (hcop : Nat.Coprime y x) :
    ¬HasESEReal (amp5 (y : ℝ) (x : ℝ)) ↔ y = 1 := by
  sorry

/-- Target 3 (Theorem 3): Complete `6 × 6` critical even symmetric PST dichotomy. -/
theorem target_theorem_3_6x6 {p q r : ℕ} (hp_odd : Odd p) (hq_odd : Odd q) (hr_odd : Odd r)
    (hpq : p < q) (hqr : q < r) (hgap1 : (q - p) % 4 = 2) (hgap2 : (r - q) % 4 = 2) :
    ¬HasESEReal (amp6 (p : ℝ) (q : ℝ) (r : ℝ)) ↔ p = 1 := by
  sorry

/-- Target 4 (Theorem 4): Complete resolution of Conjecture 4.1 (`7 × 7`, reduced). -/
theorem target_theorem_4_conjecture_4_1 {x y z : ℕ} (hx_odd : Odd x) (hy_even : Even y)
    (hz_odd : Odd z) (hxy : x < y) (hyz : y < z) (hcop : Nat.gcd x (Nat.gcd y z) = 1) :
    ¬HasESEReal (amp7 (x : ℝ) (y : ℝ) (z : ℝ)) ↔ (x ∣ y ∧ x ∣ z) := by
  sorry

/-- Target 5 (Theorem 4, Unreduced): Real-scaled `7 × 7` Conjecture 4.1. -/
theorem target_theorem_4_conjecture_4_1_unreduced {c : ℝ} (hc : 0 < c) {x y z : ℕ}
    (hx_odd : Odd x) (hy_even : Even y) (hz_odd : Odd z) (hxy : x < y) (hyz : y < z) :
    (∀ τ : ℝ, 0 < τ → τ < Real.pi / (c * (Nat.gcd x (Nat.gcd y z) : ℝ)) →
      amp7 (c * (x : ℝ)) (c * (y : ℝ)) (c * (z : ℝ)) τ ≠ 0) ↔
    (x ∣ y ∧ x ∣ z) := by
  sorry

/-- Target 6 (Theorem 5): Sharp even rupture dimension `N_crit^even = 8`. -/
theorem target_theorem_5_even_rupture_8x8 {m : ℕ} (hm : 1 ≤ m) :
    let M : ℝ := (4 * m + 5 : ℕ)
    amp8 1 (M - 2) M (M + 2) (2 * Real.pi / M) < 0 ∧
    HasESEReal (amp8 1 (M - 2) M (M + 2)) := by
  sorry

/-- Target 7 (Theorem 6): Critical `9 × 9` No-ESE Theorem (ALL `1 < b < c < d`). -/
theorem target_theorem_6_critical_9x9 {b c d : ℕ}
    (h1b : 1 < b) (hbc : b < c) (hcd : c < d)
    (hb_even : Even b) (hc_odd : Odd c) (hd_even : Even d) :
    ∀ t : ℝ, 0 ≤ t → t < Real.pi → 0 < amp9 1 (b : ℝ) (c : ℝ) (d : ℝ) t := by
  sorry

/-- Target 8 (Theorem 7): Exact `11 × 11` odd rupture threshold `m ≥ 6` (`M* = 12`). -/
theorem target_theorem_7_odd_rupture_11x11 {m : ℕ} (hm : 1 ≤ m) :
    HasESEReal (amp11 1 (2 * m : ℕ) (2 * m + 1 : ℕ) (2 * m + 2 : ℕ) (2 * m + 3 : ℕ)) ↔ 6 ≤ m := by
  sorry

/-- Target 9 (Theorem 8): Universal `(R, r)` Krawtchouk-core vs. spectral-cluster phase transition. -/
theorem target_theorem_8_universal_3R_plus_2 {R : ℕ} (hR : 2 ≤ R) :
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
  sorry

/-- Target 10 (Theorem 9): Infinite non-symmetric staggered-field complex-amplitude ESE family `J_{a,b}`. -/
theorem target_theorem_9_nonsymmetric_family {a k : ℕ} (ha_odd : Odd a) (ha_ndvd3 : ¬(3 ∣ a)) :
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
  sorry

/-- Target 11 (Theorem 10A): Exact Jacobi energy variance `b₀²` and Mandelstam-Tamm ESE speed limit. -/
theorem target_theorem_10a_qsl_and_variance :
    (∀ {n : ℕ} (hn : 2 ≤ n) (a b : Fin n → ℝ),
      ∑ i : Fin n,
        ((jacobiMatrix a b) i ⟨0, by omega⟩ -
          (if i = ⟨0, by omega⟩ then a ⟨0, by omega⟩ else 0)) ^ 2 =
        (b ⟨0, by omega⟩) ^ 2) ∧
    (∀ {n : ℕ} (lam w : Fin n → ℝ) (μ σ τ : ℝ),
      (∀ k, 0 ≤ w k) → (∑ k : Fin n, w k = 1) →
      (∑ k : Fin n, w k * lam k = μ) →
      (∑ k : Fin n, w k * (lam k - μ) ^ 2 = σ ^ 2) →
      0 < σ → 0 < τ → returnAmpComplex lam w τ = 0 →
      Real.pi / (2 * σ) ≤ τ) := by
  sorry

/-- Target 12 (Theorem 10B): Exact ESE ↔ Early Target Exclusion (ETE) time-reversal duality. -/
theorem target_theorem_10b_ese_ete_duality {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ)
    (u : Fin n → Fin n → ℝ) (T : ℝ) (η : ℂ) (hη : Complex.normSq η = 1)
    (hparity : ∀ k : Fin n, u k ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ = (-1 : ℝ) ^ (k : ℕ) * u k ⟨0, hn⟩)
    (hpst : ∀ k : Fin n, Complex.exp (-Complex.I * (lam k : ℂ) * (T : ℂ)) = η * (-1 : ℂ) ^ (k : ℕ))
    (t : ℝ) :
    Complex.normSq (targetAmpComplex hn lam u (T - t)) =
      Complex.normSq (returnAmpComplex lam (fun k => (u k ⟨0, hn⟩) ^ 2) t) := by
  sorry

end SpectralEclipse.ComparatorTarget

end
