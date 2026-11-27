# AGENTS.md

Canonical instructions for every coding agent working in this repository (Codex, OpenCode, Claude Code, Gemini CLI, Antigravity, Cursor, Grok Build, Grok Bot and others).
`CLAUDE.md`, `GEMINI.md`, `.cursor/rules/build-standard.mdc` and `llms.txt` only point here. Edit this file, never the pointers.
Full standard: `docs/build-standard.md` (Build Standard for LLMs v1.2.0, 90 items).

## Project

- **Name:** `spectral-eclipse-frontier`
- **Purpose:** Machine-checked Lean 4.35.0 proofs (6-kernel Palomar verified) and 8-language computational observatory resolving a 10-theorem chain of open problems in quantum spin-chain Early State Exclusion (ESE), including Conjecture 4.1 of Escobar-Garcia-Minenkova (arXiv:2507.18767v1), the exact $4\times 4 / 5\times 5 / 6\times 6 / 7\times 7 / 9\times 9$ classification, sharp rupture thresholds $N_{\mathrm{crit}}^{\mathrm{even}} = 8$ and $N_{\mathrm{crit}}^{\mathrm{odd}} = 11$ ($M^* = 12$), the universal $(R, r)$ phase boundary $N_{\mathrm{crit}}(R) = 3R + 2$, the first infinite non-symmetric staggered-field complex-amplitude ESE family $J_{a,b}$, and the exact QGTL Mandelstam-Tamm speed limit $\tau_{\mathrm{ESE}} \ge \pi/(2b_0)$.
- **Author / Owner:** Alexander Stephen Donahue (`Alexander S. Donahue`, ORCID `0009-0006-8168-9648`, Independent Researcher, Spokane, WA, USA; `https://github.com/0thernes`)
- **Manifest:** `repo.yaml` (validated against `repo-standard.schema.json`)
- **Stack:** Lean 4.35.0 + Mathlib v4.35.0, NASM x86-64 AVX2+FMA Assembly, ISO C11, C++20, Rust 1.94.1 (`#![forbid(unsafe_code)]`), Zig 0.17.0 (`std.math.big.int`), Eshkol v1.3.6-evolve (dual-number AD), Node.js + Moonlab WASM, QGTL + Quantum-RNG, Python 3.9+/3.12, Tectonic 0.17.0 (AMS-LaTeX).
- **Layout:**
  - `lean/` — Lean 4.35.0 proof library (`SpectralEclipse/`), isolated `Challenge.lean`, `Solution.lean`, `VerifyAxioms.lean`, `comparator.json`.
  - `engines/` — 8 independent computational engines (`asm/`, `c/`, `cpp/`, `rust/`, `zig/`, `eshkol/`, `moonlab/`, `qgtl_qrng/`).
  - `third_party/` — Vendored MIT/Apache-2.0 Moonlab, QGTL, and Quantum-RNG sources with explicit provenance.
  - `reference/` & `python/` — Exact arbitrary-precision integer Sturm & Hochstadt reference oracle and Python package.
  - `tests/` — Falsifiable, negative, regression, golden, property (Hypothesis), differential, metamorphic, fuzz, and mutation tests.
  - `paper/` & `dist/` — AMS-LaTeX manuscript, vector PDF figures, frozen compiled PDF, standalone `arxiv_submission.tar.gz`.
  - `web/` — Interactive Spectral Eclipse Observatory & Lean 4 Proof Blueprint DAG (GitHub Pages).
  - `scripts/`, `docs/`, `data/`, `results/`, `examples/` — Audit, citation, timestamping, build scripts, ADRs, logs, and manifests.
- **Status:** active

## Commands

Use the task runner (`justfile`, A31). Every command works from a clean clone:

- `just setup`: verify pinned toolchains and install Python dependencies
- `just build`: build Lean 4 library + all native engines (ASM/C/C++/Rust/Zig/QGTL+QRNG)
- `just verify-lean`: build Lean 4, run `VerifyAxioms.lean`, Batteries linter, negative tamper check, and `leanchecker`
- `just test`: run all Python, engine, differential, property, metamorphic, negative, and mutation tests
- `just lint`: report-only linters (`ruff`, `mypy`, `cargo clippy`, Batteries linter)
- `just bench`: honest multi-engine benchmarks with medians and interquartile spread
- `just paper`: regenerate figures, compile AMS-LaTeX PDF via Tectonic (0 overfull hboxes), and build standalone `arxiv_submission.tar.gz`
- `just reproduce`: clean clone to headline verified results
- `just audit`: run Build Standard v1.2.0 and Playbook v1.3 repo audit (`scripts/audit_repo.py`)
- `just release X.Y.Z`: bump `VERSION`, tag `vX.Y.Z`, and push

## Hard rules

- R1. Nothing may gate, block or slow a commit or push. No branch protection, no required status checks, no commit or tag signing requirements, no git hooks, no push protection, no merge queues, and no coverage, lint, SAST or SBOM requirement that fails or blocks anything; those tools may only report.
- R2. Commit and push straight to `main`. No pull requests and no feature branches. Fixes for failing checks are follow-up commits to `main`.
- R3. CI is informational. CI reports results on every push. A red CI run is a finding to fix, never a barrier.
- R4. Banned tools and files. No Dependabot or Renovate auto-PRs, no PR templates, no CodeRabbit, no Copilot review or `.github/copilot-instructions.md`, no `FUNDING` file.
- R5. One-person lean, not corporate. Prefer plain text, reproducible scripts, and auditable artifacts over heavyweight process.
- R6. Never fabricate. Every claim, theorem, citation, number, badge, screenshot, and test result must come from a real run of the current code. Unverified means labeled unverified.
- R7. Classify every finding. Each finding is exactly one of: `bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`.
- R8. Precedence when rules collide: Owner's explicit instruction > hard rules R1-R8 > Build Standard v1.2.0 items > ecosystem conventions.

## Finding classes

- `bug`: Defect in program logic (code runs differently from specification or intent).
- `error`: Wrong artifact or failed execution outside program logic (wrong number, claim, doc, config, version, build, or command).
- `issue`: Weakness in something that exists (works and is not wrong, but unclear, inconsistent, fragile, or hard to maintain).
- `problem`: External obstacle blocking progress not caused by the project's own artifacts.
- `concern`: Risk that has not caused harm yet (could fail, mislead, or create security/legal exposure later).
- `dilemma`: Trade-off between valid options depending on owner priorities.
- `conflict`: Two requirements, sources, or rules contradict each other.
- `gap`: Required or expected artifact/item does not exist yet.
- `hole`: Missing check or safeguard that could let a defect pass unnoticed.
- `blindspot`: Unexamined platform, failure mode, or assumption.

## Known traps

- **Windows ReFS bracket path:** Local path contains `[Vibe Coded (AI)]`. In PowerShell ALWAYS pass `-LiteralPath` to file cmdlets (`Test-Path -LiteralPath`, `Get-ChildItem -LiteralPath`, etc.).
- **Author affiliation:** Always `Independent Researcher, Spokane, WA, USA` (never `0thernes LLC`).
- **Float64 cancellation near $t = \pi$:** Never judge ESE near the $2n$-th order root $t = \pi$ using naive $\sum c_k \cos(\lambda_k t)$ in IEEE-754 float64; always use the exact cancellation-free $\sin^2(\lambda_k u)$ representation ($t = \pi - 2u$) or exact integer Sturm sequences.
- **Lean 4.35 module header:** Every `.lean` proof file MUST start with `module` (Palomar spec) and avoid `sorry`, `admit`, `native_decide`, `unsafe`, custom `axiom`, `partial def`, or `@[extern]`.
- **Dual-ABI NASM assembly:** `engines/asm/jacobi_avx2.asm` must conditionally compile both Win64 (RCX, RDX, R8, R9) and SysV AMD64 (RDI, RSI, RDX, RCX) register conventions so Windows and Linux CI both assemble and link cleanly.
