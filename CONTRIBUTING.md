# Contributing to `spectral-eclipse-frontier`

Thank you for your interest in auditing, extending, or independently replicating this work.

## Workflow & Hard Rules

1. Read `AGENTS.md` before making changes.
2. This is a single-maintainer research repository (`main` is updated directly; no PR templates or auto-PR bots are used). External contributors may open GitHub Issues using the structured templates in `.github/ISSUE_TEMPLATE/` to report mathematical counterexamples, statement-fidelity concerns, build issues, or independent replication reports.
3. Classify every finding into exactly one of the 10 Build Standard v1.2.0 classes (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`).

## Verification Bar

Any change affecting proofs, engines, or claims must preserve:
- Zero `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` tokens across `lean/SpectralEclipse/` and `lean/Solution.lean`.
- Exhaustive `#print axioms` strictly within `[propext, Classical.choice, Quot.sound]`.
- Zero differential mismatches across all 8 computational engines and the exact integer Sturm oracle.
- Zero warnings/overfull hboxes in `paper/main.tex` via `tectonic -X compile main.tex`.
- Dual licensing: code contributions under `Apache-2.0`, documentation/manuscript contributions under `CC-BY-4.0`.
