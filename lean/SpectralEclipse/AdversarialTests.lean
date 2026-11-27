/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public import SpectralEclipse.NonVacuity
import Mathlib.Tactic

/-!
# Machine-Checked Adversarial Refutations of Naive / False Conjecture Variants

Proves directly inside the Lean 4 kernel that every natural over-generalization of
Conjecture 4.1 (`arXiv:2507.18767v1`) is **FALSE**, demonstrating why the sharp
dimension thresholds `N_crit^even = 8` and `N_crit^odd = 11` (`M* = 12`) are genuinely tight:
  1. `refute_even_8x8_naive_divisibility`: `p₁ = 1` dividing all eigenvalues does NOT prevent
     ESE at `8 × 8` (explicit counterexample `{±1/2, ±7/2, ±9/2, ±11/2}`).
  2. `refute_odd_11x11_naive_divisibility`: `λ₁ = 1` dividing all eigenvalues does NOT prevent
     ESE at `11 × 11` (explicit counterexample `{0, ±1, ±12, ±13, ±14, ±15}`).
  3. `refute_11x11_threshold_m5`: The sharp threshold `M* = 12` (`m ≥ 6`) CANNOT be lowered to
     `m = 5` (`{0, ±1, ±10, ±11, ±12, ±13}` has NO ESE).
  4. `refute_5x5_nonsym_no_ESE_assumption`: Dropping diagonal symmetry (`a₀ = a₁`) breaks the
     `5 × 5` no-ESE rule even when minimal gap `a = 1` divides `b = 4` (`J_{1,4}` has exact
     complex ESE at `τ = π/3`).
  5. `refute_qsl_saturation_for_J14`: `J_{1,4}` strictly satisfies `π/(2 b₀) < τ_ESE = π/3`
     (strictly below QSL saturation, `η = 3/(2√15) ≈ 0.3873 < 1`).
-/

@[expose] public section

namespace SpectralEclipse.AdversarialTests

/-- Refutes the naive extension of the `4 × 4` / `6 × 6` even dichotomy to `8 × 8`:
`p₁ = 1` does NOT imply absence of ESE at `8 × 8`. -/
theorem refute_even_8x8_naive_divisibility :
    ¬(∀ q r s : ℕ, Odd q → Odd r → Odd s → 1 < q → q < r → r < s →
      (q - 1) % 4 = 2 → (r - q) % 4 = 2 → (s - r) % 4 = 2 →
      ¬HasESEReal (amp8 1 (q : ℝ) (r : ℝ) (s : ℝ))) := by
  intro hall
  have h := hall 7 9 11 ⟨3, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  norm_num at h
  exact h NonVacuity.witness_8x8_rupture_m1

/-- Refutes the naive extension of Conjecture 4.1 (`5 × 5, 7 × 7, 9 × 9`) to `11 × 11`:
`λ₁ = 1` dividing all eigenvalues does NOT imply absence of ESE at `11 × 11`. -/
theorem refute_odd_11x11_naive_divisibility :
    ¬(∀ l2 l3 l4 l5 : ℕ, Even l2 → Odd l3 → Even l4 → Odd l5 →
      1 < l2 → l2 < l3 → l3 < l4 → l4 < l5 →
      ¬HasESEReal (amp11 1 (l2 : ℝ) (l3 : ℝ) (l4 : ℝ) (l5 : ℝ))) := by
  intro hall
  have h := hall 12 13 14 15 ⟨6, rfl⟩ ⟨6, rfl⟩ ⟨7, rfl⟩ ⟨7, rfl⟩
    (by decide) (by decide) (by decide) (by decide)
  norm_num at h
  exact h NonVacuity.witness_11x11_supercrit_m6

/-- Refutes lowering the sharp `11 × 11` rupture threshold from `m ≥ 6` (`M* = 12`) to `m ≥ 5`. -/
theorem refute_11x11_threshold_m5 :
    ¬(∀ m : ℕ, 5 ≤ m →
      HasESEReal (amp11 1 (2 * m : ℕ) (2 * m + 1 : ℕ) (2 * m + 2 : ℕ) (2 * m + 3 : ℕ))) := by
  intro hall
  have h := hall 5 (by decide)
  norm_num at h
  exact NonVacuity.witness_11x11_subcrit_m5 h

/-- Refutes extending the symmetric `5 × 5` no-ESE rule to persymmetric non-symmetric chains:
`J_{1,4}` is persymmetric, has exact PST at `π`, minimal gap `1`, yet complex ESE at `π/3`. -/
theorem refute_5x5_nonsym_no_ESE_assumption :
    ∃ (a b : Fin 5 → ℝ) (lam : Fin 5 → ℝ) (u : Fin 5 → Fin 5 → ℝ),
      IsPersymmetricJacobi a b ∧ a 0 ≠ a 1 ∧
      spectralState lam u Real.pi 4 = 1 ∧
      HasESEComplex (fun t => spectralState lam u t 0) Real.pi := by
  have h := theorem_9_nonsymmetric_family (a := 1) (k := 0) ⟨0, rfl⟩ (by decide)
  norm_num at h
  exact ⟨stagDiag 1 4, stagHop 1 4, stagEigvals 1 4, stagEigvecs 1 4,
    h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Refutes claiming `J_{1,4}` saturates the Mandelstam-Tamm QSL (`π / (2 b₀) ≠ π / 3`). -/
theorem refute_qsl_saturation_for_J14 :
    Real.pi / (2 * Real.sqrt 15) ≠ Real.pi / 3 :=
  ne_of_lt NonVacuity.witness_J14_qsl_variance.2

end SpectralEclipse.AdversarialTests
