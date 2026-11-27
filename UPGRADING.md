# Upgrading & Deprecation Policy (`A41`)

`spectral-eclipse-frontier` follows [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html) anchored to the single canonical version file [`VERSION`](VERSION).

## Release History & Migration Notes

### `v1.1.0` (Current Release — November 27, 2026)
- **Additive & Non-Breaking:** All 12 isolated Palomar target theorem signatures in `lean/Challenge.lean` are unchanged from `v1.0.0`.
- **New Public Python Constants:** `FLOAT64_CANCELLATION_MARGIN` (`1e-11`) and `FLOAT64_MIN_RE_THRESHOLD` (`1e-10`) are now explicitly defined in `python/spectral_eclipse/core.py` and exported in `python/spectral_eclipse/__init__.py`.
- **New Lean Non-Vacuity Witnesses:** Added 3 additional concrete witnesses in `lean/SpectralEclipse/NonVacuity.lean` (`witness_7x7_unreduced_c2_3_6_9`, `witness_universal_3R_plus_2_R3`, `witness_J14_ese_ete_duality`), raising audited declarations from 568 to 571 (52 explicit `#print axioms`).
- **CVE Remediation (`requirements.txt`):** Removed unused `PyMuPDF`, upgraded `pillow==13.0.0`, `pytest==9.2.0`, and pinned `pygments==2.21.0` (0 open Dependabot alerts, 0 `osv-scanner` CVEs).
- **QRNG Numerical Optimizer Fix (`DEVIATIONS.md`):** Fixed single-bracket boundary trapping in `engines/qgtl_qrng/se_qgtl_qrng.c` (`compute_interior_min`) while keeping the pre-registered window, arms, seeds, and statistical tests strictly unchanged.

### `v1.0.0` (Initial Frozen Release — November 27, 2026)
- Initial public release. Immutable tag preserved (`8d6cf7c`).

## Compatibility & Stability Guarantees

1. **Lean 4 Formal Target Signatures (`lean/Challenge.lean`):**
   - The 12 isolated Palomar target theorem signatures in `lean/Challenge.lean` are treated as immutable within major version `1.x.y`.
   - Any mathematical correction or strengthened theorem statement in a future `1.x` release will be added alongside existing targets and documented transparently in [`ERRATA.md`](ERRATA.md) and [`CHANGELOG.md`](CHANGELOG.md); breaking signature changes require a major version bump (`2.0.0`).
2. **Python Package Public API (`python/spectral_eclipse/__init__.py`):**
   - Exact exported symbols: `JacobiChain`, `FLOAT64_CANCELLATION_MARGIN`, `FLOAT64_MIN_RE_THRESHOLD`, `persymmetric_weights`, `reconstruct_persymmetric_jacobi`, `return_amplitude`, `target_amplitude`, and `detect_real_ese`.
   - All exported symbols remain backward-compatible across `1.x.y`. Any future deprecation will emit a standard `DeprecationWarning` for at least one minor release cycle before removal in a major release.
3. **Artifact & Checksum Immutability:**
   - Frozen PDFs (`dist/Donahue_2026_spectral_eclipse_frontier.pdf`), `dist/arxiv_submission.tar.gz`, `data/MANIFEST.sha256`, and cryptographic timestamps (`.tsr`, `.ots`) are never silently rewritten under an existing git tag.
4. **Toolchain Pinning:**
   - Lean 4 toolchain (`leanprover/lean4:v4.35.0`) and Mathlib commits are pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`. Upgrading Lean/Mathlib will be performed in a dedicated minor or major release after full 6-kernel `lake comparator --paranoid` verification passes.
