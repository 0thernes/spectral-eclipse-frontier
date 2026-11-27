# ADR-0002: Dual Licensing (`Apache-2.0` + `CC-BY-4.0`) and Six-Kernel Palomar Comparator Isolation

- **Status:** Accepted
- **Date:** 2026-11-26
- **Author:** Alexander Stephen Donahue

## Context

Scientific repositories containing both executable software / Lean formalizations and academic white papers / figures face two recurring pitfalls: (a) applying a software-only license to prose/figures creates ambiguity for academic reuse, and (b) checking formal proofs only with the standard `lean` binary leaves open subtle bugs in specification definitions or single-kernel soundness.

## Decision

1. **Dual License:** License all software, Lean 4 proof modules, polyglot engines, tests, and CI scripts under **`Apache-2.0`** (`LICENSE`), and all manuscript sources, compiled PDFs, figures, and documentation prose under **`CC-BY-4.0`** (`LICENSE-DOCS`), with explicit SPDX headers and third-party attribution in `THIRD_PARTY_NOTICES.md` and `NOTICE`.
2. **Palomar Comparator Isolation:** Separate target theorem statements into a standalone Mathlib-only `lean/Challenge.lean` (12 isolated targets), bridge them via a sorry-free `lean/Solution.lean`, configure `lean/comparator.json`, and run `lake comparator --config comparator.json --paranoid` inside `bubblewrap` on Ubuntu 24.04 CI to replay every proof through **6 independent Lean 4.35.0 checkers** (`lean`, `leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
3. **Live Negative Gate:** Pair positive kernel checks with `lean/SpectralEclipse/NonVacuity.lean`, `lean/SpectralEclipse/AdversarialTests.lean`, and `scripts/test_lean_negative.py` to prove that mutated false statements are actively rejected.

## Consequences

- **Positive:** Maximum legal clarity for both software engineers and academic readers, and zero single-kernel trust bottleneck.
- **Trade-off:** Maintaining exact signature parity between `Challenge.lean`, `Solution.lean`, and `SpectralEclipse/*.lean` adds structural discipline documented in `docs/statement-fidelity.md`.
