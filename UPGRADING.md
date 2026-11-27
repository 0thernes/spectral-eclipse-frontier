# Upgrading & Deprecation Policy (`A41`)

`spectral-eclipse-frontier` follows [Semantic Versioning 2.0.0](https://semver.org/spec/v2.0.0.html) anchored to the single canonical version file [`VERSION`](VERSION).

## Current Release: `v1.0.0` (Initial Frozen Release)

`v1.0.0` is the initial public release. There are no prior versions to migrate from and no deprecated interfaces.

## Compatibility & Stability Guarantees

1. **Lean 4 Formal Target Signatures (`lean/Challenge.lean`):**
   - The 12 isolated Palomar target theorem signatures in `lean/Challenge.lean` are treated as immutable within major version `1.x.y`.
   - Any mathematical correction or strengthened theorem statement in a future `1.x` release will be added alongside existing targets or documented transparently in [`ERRATA.md`](ERRATA.md) and [`CHANGELOG.md`](CHANGELOG.md); breaking signature changes require a major version bump (`2.0.0`).
2. **Python Package Public API (`python/spectral_eclipse/`):**
   - Exported functions (`hochstadt_reconstruct`, `return_amplitude`, `detect_ese`, `sturm_root_count`, `qsl_bound`, `staggered_j_ab`, `FLOAT64_CANCELLATION_MARGIN`) remain backward-compatible across `1.x.y`.
   - Any future deprecation will emit a standard `DeprecationWarning` for at least one minor release cycle before removal in a major release.
3. **Artifact & Checksum Immutability:**
   - Frozen PDFs (`dist/Donahue_2026_spectral_eclipse_frontier.pdf`), `dist/arxiv_submission.tar.gz`, `data/MANIFEST.sha256`, and cryptographic timestamps (`.tsr`, `.ots`) are never silently rewritten under an existing git tag.
4. **Toolchain Pinning:**
   - Lean 4 toolchain (`leanprover/lean4:v4.35.0`) and Mathlib commits are pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`. Upgrading Lean/Mathlib will be performed in a dedicated minor or major release after full 6-kernel `lake comparator --paranoid` verification passes.
