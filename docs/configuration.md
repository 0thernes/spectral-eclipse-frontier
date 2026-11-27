# Configuration Reference

The repository runs deterministically out of the box with zero mandatory environment variables or API keys. Optional configuration overrides are documented below and mirrored in `.env.example`.

## Environment Variables

| Variable | Default | Scope | Description |
| :--- | :--- | :--- | :--- |
| `PYTHONUTF8` | `1` (recommended on Windows) | Python scripts & CI | Forces UTF-8 I/O across Windows, Linux, and macOS. |
| `ESHKOL_BIN` | Auto-discovered on `PATH` / `Z:\Tools\eshkol\...` | `engines/eshkol/run_eshkol.py` | Explicit path to `eshkol-run` binary. When absent, automatically falls back to exact pure-Python dual-number arithmetic with parity logging. |
| `LEAN_PATH` | Managed by `lake` | `lean/` | Automatically configured by `lake env`; do not override manually. |

## Build Configuration Files

- `lean/lean-toolchain`: Pins `leanprover/lean4:v4.35.0`.
- `lean/lakefile.toml`: Enforces `autoImplicit = false`, `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`, and registers libraries `SpectralEclipse`, `Challenge`, `Solution`, `VerifyAxioms`.
- `lean/comparator.json`: Configures the 12 isolated Palomar targets and strict axiom allowlist `["propext", "Quot.sound", "Classical.choice"]`.
- `pyproject.toml` & `requirements.txt`: Pin Python package metadata, `ruff`, `mypy --strict`, `pytest`, and exact dependency versions.
- `.gitleaks.toml`: Secret-scanning configuration (zero secrets tracked).
- `.editorconfig` & `.gitattributes`: Enforce UTF-8 and LF line endings across all text, Lean, TeX, and script files (required for cross-OS SHA-256 manifest determinism).
