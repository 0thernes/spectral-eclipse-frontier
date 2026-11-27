# Errata & Post-Release Corrections

This file tracks every mathematical, formalization, numerical, bibliographic, or software correction discovered after `v1.0.0` (Playbook v1.3 #39 / Build Standard v1.2.0).

## Resolved Errata (`v1.0.0` -> `v1.1.0`, 2026-11-27)

None of the errata below altered any machine-checked Lean 4 theorem statement, proof soundness, axiom footprint, or pre-registered hypothesis verdict (H1–H3 significant, H4 null). All corrections are permanently archived in `v1.1.0` and documented in `DEVIATIONS.md` and `HARDENING_LOG.md`:

| ID | Class | Location (`v1.0.0`) | Defect Description | Resolution (`v1.1.0`) |
| :--- | :--- | :--- | :--- | :--- |
| **E-01** | `bug` | `engines/qgtl_qrng/se_qgtl_qrng.c` (`compute_interior_min`) | Single-bracket golden-section refinement trapped near the upper grid boundary on $J_{1,4}$ at $\varepsilon = 0$, reporting $m(J_{1,4}, 0) = 1.655 \times 10^{-3}$ instead of exact $0$. | Refined every local-minimum bracket on the exact same 500-point grid; all four arms now return exact $0.000$ at $\varepsilon = 0$. Re-ran study, regenerated `results/qgtl_qrng_{study,analysis}.json`, Figure 5, and Table 4; logged as Deviation #1 in `DEVIATIONS.md`. |
| **E-02** | `error` | `paper/main.tex` (Section 3, Proof of Theorem 6) | Prose wrote $H_e''(w) > 0$ on $(0, 4.5^2]$ instead of the proved domain $(0, 5.5^2]$ (`(11/2)^2` in `lean/SpectralEclipse/TrigBounds.lean`). | Corrected to $(0, 5.5^2]$ to match the machine-checked theorem verbatim. |
| **E-03** | `error` | `paper/main.tex` (Section 7, Disorder Model) | Disorder Hamiltonian omitted the explicit average-hopping normalization factor $\bar{b}$ present in `engines/qgtl_qrng/se_qgtl_qrng.c` ($J_\varepsilon = J + \varepsilon \bar{b}\,\mathrm{diag}(\xi)$) and the $\delta = 0.05 T_0$ exclusion margin. | Restored exact $\bar{b}$ normalization and $\delta = 0.05 T_0$ margin in Section 7. |
| **E-04** | `error` | `docs/run-log.md` | H2 and H3 descriptions were transposed, Cliff's $\delta$ values for H1/H3/H4 were misquoted, H4 listed $\varepsilon = 0.02$ instead of $0.05$, and the CLI command included a non-existent `--study` flag. | Corrected all numbers against `results/qgtl_qrng_analysis.json`, fixed CLI invocation, and recorded both `v1.0.0` and `v1.1.0` runs. |
| **E-05** | `error` | `UPGRADING.md`, `docs/verification.md`, `docs/architecture.md`, `docs/benchmarks.md`, `THIRD_PARTY_NOTICES.md` | Documentation contained stale or mismatched symbol names (`hochstadt_reconstruct`, `witness_4x4_even_p2`, `moonlab_xy_sim.mjs`, `Rayon` instead of `std::thread`) and stale counts (`0/1,900` instead of `0/2,000`, `0TH-2026-020`/`022` instead of `0TH-2026-024`, `280` vs. `290` lines in `Challenge.lean`). | Synchronized every symbol, filename, line count, and registry ID against live source files and enforced automated regression checks in `tests/test_all.py`. |
| **E-06** | `concern` | `requirements.txt` | Pinned `pillow==11.3.0`, unused `PyMuPDF==1.26.5`, `pytest==8.4.2`, and transitive `pygments==2.9.0` triggered 62 GitHub Dependabot alerts and 65 `osv-scanner` advisories. | Removed unused `PyMuPDF`, upgraded `pillow==13.0.0` and `pytest==9.2.0`, and pinned `pygments==2.21.0` (0 Dependabot alerts, 0 `osv-scanner` CVEs). |
| **E-07** | `error` | Linux CI (`ci.yml`, `lean-verify.yml`) | 13 shebang Python scripts lacked POSIX `+x` mode (`ruff EXE001`), `scripts/build_blueprint.py` had 1 `mypy --strict` error, and `hochstadtWeightOdd` lacked a docstring (`runLinter docBlame`), all masked by `continue-on-error: true`. | Fixed all 15 static-analysis findings, promoted Batteries `runLinter` to a hard CI gate, and separated `ruff` and `mypy --strict` into distinct CI steps. |

## Active Errata

*None open as of `v1.1.0` (2026-11-27).*

## Withdrawal & Retraction Policy

If a substantive mathematical error is ever discovered in a claimed theorem or proof that cannot be repaired while preserving the statement, we will: (1) immediately log a dated entry in this file and `CHANGELOG.md`, (2) publish a corrective release with updated Lean 4 artifacts or explicit retraction notice in `paper/main.tex` and `README.md`, (3) update record `0TH-2026-024` in `0thernes-research-archive`, and (4) never silently rewrite or delete historical git tags (`v1.0.0`, `v1.1.0`).

## Reporting Errata

If you identify a discrepancy in any theorem statement, Lean 4 proof, engine output, figure, or citation, please open a GitHub Issue (labeled with the matching Build Standard finding class) or email `0_0@0thernes.art`. Verified corrections are logged here with the affected commit SHA, finding class, impact assessment, and fixing commit SHA.
