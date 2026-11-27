/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
-- SPDX-FileCopyrightText: 2026 Alexander S. Donahue
-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean
import all SpectralEclipse.Defs
import all SpectralEclipse.TrigBounds
import all SpectralEclipse.Chains456
import all SpectralEclipse.Conjecture41
import all SpectralEclipse.RuptureAndPhase
import all SpectralEclipse.Critical9x9Certs
import all SpectralEclipse.Critical9x9
import all SpectralEclipse.NonSymmetricFamily
import all SpectralEclipse.SpeedLimitAndDuality
import all SpectralEclipse.NonVacuity
import all SpectralEclipse.AdversarialTests
import all SpectralEclipse
import all Solution

/-!
# Exhaustive Axiom Audit for Spectral Eclipse Frontier (Theorems 1–10)

Prints `#print axioms` for:
  - All 16 primary theorems in `SpectralEclipse` (Theorems 1–10 + Schrödinger fidelity & core lemmas)
  - All 15 non-vacuity witnesses in `SpectralEclipse.NonVacuity`
  - All 5 adversarial refutations in `SpectralEclipse.AdversarialTests`
  - All 12 isolated Mathlib-only comparator target theorems in `SpectralEclipse.ComparatorTarget`
PLUS runs an exhaustive `Lean.collectAxioms` metaprogram auditing EVERY single `theorem`
declaration across the entire `SpectralEclipse` and `Solution` module trees.

Run: `cd lean && lake env lean VerifyAxioms.lean`
Every theorem must depend strictly on `[propext, Classical.choice, Quot.sound]` (or fewer).
-/

-- Primary exported theorems (16 declarations)
#print axioms SpectralEclipse.schrodinger_solution_fidelity
#print axioms SpectralEclipse.even_hasESE_of_min_ge_three
#print axioms SpectralEclipse.dichotomy_4x4
#print axioms SpectralEclipse.dichotomy_5x5
#print axioms SpectralEclipse.dichotomy_6x6
#print axioms SpectralEclipse.conjecture_4_1_7x7
#print axioms SpectralEclipse.conjecture_4_1_7x7_unreduced
#print axioms SpectralEclipse.even_rupture_8x8
#print axioms SpectralEclipse.odd_critical_9x9_no_ESE
#print axioms SpectralEclipse.odd_rupture_11x11_threshold
#print axioms SpectralEclipse.cluster_self_gap_sum
#print axioms SpectralEclipse.universal_phase_transition_3R_plus_2
#print axioms SpectralEclipse.theorem_9_nonsymmetric_family
#print axioms SpectralEclipse.jacobi_energy_variance_eq_b0_sq
#print axioms SpectralEclipse.spectral_variance_eq_b0_sq
#print axioms SpectralEclipse.mandelstam_tamm_ese_bound
#print axioms SpectralEclipse.ese_ete_duality

-- Non-vacuity witnesses (15 declarations)
#print axioms SpectralEclipse.NonVacuity.witness_4x4_noESE_1_3
#print axioms SpectralEclipse.NonVacuity.witness_4x4_ESE_3_5
#print axioms SpectralEclipse.NonVacuity.witness_5x5_noESE_1_2
#print axioms SpectralEclipse.NonVacuity.witness_5x5_ESE_3_4
#print axioms SpectralEclipse.NonVacuity.witness_6x6_noESE_1_3_5
#print axioms SpectralEclipse.NonVacuity.witness_6x6_ESE_3_5_7
#print axioms SpectralEclipse.NonVacuity.witness_7x7_noESE_1_2_3
#print axioms SpectralEclipse.NonVacuity.witness_7x7_ESE_3_4_5
#print axioms SpectralEclipse.NonVacuity.witness_8x8_rupture_m1
#print axioms SpectralEclipse.NonVacuity.witness_9x9_noESE_1_2_3_4
#print axioms SpectralEclipse.NonVacuity.witness_9x9_noESE_1_20_21_22
#print axioms SpectralEclipse.NonVacuity.witness_11x11_subcrit_m5
#print axioms SpectralEclipse.NonVacuity.witness_11x11_supercrit_m6
#print axioms SpectralEclipse.NonVacuity.witness_J14_staggered_complex_ESE
#print axioms SpectralEclipse.NonVacuity.witness_J14_qsl_variance

-- Machine-checked adversarial refutations (5 declarations)
#print axioms SpectralEclipse.AdversarialTests.refute_even_8x8_naive_divisibility
#print axioms SpectralEclipse.AdversarialTests.refute_odd_11x11_naive_divisibility
#print axioms SpectralEclipse.AdversarialTests.refute_11x11_threshold_m5
#print axioms SpectralEclipse.AdversarialTests.refute_5x5_nonsym_no_ESE_assumption
#print axioms SpectralEclipse.AdversarialTests.refute_qsl_saturation_for_J14

-- Isolated Mathlib-only Comparator solution bridge (12 declarations)
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_1_4x4
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_2_5x5
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_3_6x6
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_4_conjecture_4_1
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_4_conjecture_4_1_unreduced
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_5_even_rupture_8x8
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_6_critical_9x9
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_7_odd_rupture_11x11
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_8_universal_3R_plus_2
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_9_nonsymmetric_family
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_10a_qsl_and_variance
#print axioms SpectralEclipse.ComparatorTarget.target_theorem_10b_ese_ete_duality

-- Exhaustive Metaprogram Audit: EVERY named & module-private theorem across all project modules
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes : Array Name :=
    #[`SpectralEclipse, `_private.SpectralEclipse, `_private.Solution]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let all := env.constants.toList.filter fun (name, info) =>
    info.isTheorem && prefixes.any (fun p => p.isPrefixOf name)
  if all.isEmpty then
    throwError "No project theorems found for exhaustive axiom audit"
  let mut bad : Array String := #[]
  for (name, _) in all do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun a => !allowed.contains a
    if !forbidden.isEmpty then
      bad := bad.push s!"{name}: {forbidden}"
  if !bad.isEmpty then
    throwError s!"Disallowed axioms detected across project theorems:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"ALL_THEOREMS_AXIOM_AUDIT_PASS: checked {all.length} theorems across SpectralEclipse — 0 disallowed axioms."
