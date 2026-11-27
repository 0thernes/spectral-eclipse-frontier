# Operations, Archival Backup & Preservation (`A35`)

`spectral-eclipse-frontier` is a static, self-contained formal-mathematics and scientific computing repository with **no deployed backend service, database, or user accounts**. Operational responsibilities focus on **long-term bit-level reproducibility, provenance preservation, and zero-drift CI maintenance**.

## 1. Multi-Tier Archival Preservation

| Tier | Mechanism | Verification Command / Target |
|---|---|---|
| **Primary Git Forge** | Public GitHub repository `0thernes/spectral-eclipse-frontier` + immutable release tag `v1.0.0` | `git clone https://github.com/0thernes/spectral-eclipse-frontier.git` |
| **Master Research Archive** | Pinned git submodule + frozen PDF + SHA-256 metadata in `0thernes/0thernes-research-archive` | `git submodule status repos/spectral-eclipse-frontier` |
| **Cryptographic Manifest** | LF-normalized SHA-256 inventory `data/MANIFEST.sha256` covering all Lean, TeX, figure, dist, and audit files | `python scripts/generate_manifest.py --verify` |
| **Trusted Timestamps** | Dual independent timestamping: DigiCert RFC 3161 (`data/MANIFEST.sha256.tsr`) + multi-calendar Bitcoin OpenTimestamps (`data/MANIFEST.sha256.ots`) | `python scripts/stamp_timestamps.py --verify` |
| **SLSA Build Provenance** | Sigstore build-provenance attestations via `actions/attest-build-provenance@v2` on CI logs & Release `v1.0.0` assets | `gh attestation verify <file> --owner 0thernes` |
| **Software Heritage** | Save Code Now snapshot archived at `https://archive.softwareheritage.org/` | SWHID recorded in `0thernes-research-archive` metadata |
| **Standalone arXiv Bundle** | Clean-room Tectonic-verified `dist/arxiv_submission.tar.gz` (zero external network fetches) | `python scripts/package_arxiv.py` |

## 2. Offline Vendoring & Toolchain Longevity

- **Lean 4.35.0 & Mathlib:** Exact toolchain pinned in `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`) and exact dependency commits pinned in `lean/lake-manifest.json`.
- **Third-Party Quantum Libraries:** Vendored directly in `third_party/{moonlab,qgtl,quantum_rng}` with full upstream copyright and licenses preserved in `THIRD_PARTY_NOTICES.md` and `NOTICE`, ensuring offline compilation decades from now without broken upstream URLs.
- **Python Environment:** Exact versions pinned in `requirements.txt` (`pytest`, `hypothesis`, `sympy`, `mpmath`, `numpy`, `scipy`, `matplotlib`, `ruff`, `mypy`, `pyyaml`, `jsonschema`).
- **Rust Dependencies:** Exact `engines/rust/Cargo.lock` committed.

## 3. Routine Maintenance & Recovery

- **Re-running CI on demand:** All four workflows (`ci.yml`, `lean-verify.yml`, `pages.yml`, `release.yml`) support `workflow_dispatch`.
- **Rebuilding from a bare clone:** Follow [`REPLICATION.md`](../REPLICATION.md) or run `just reproduce`.
- **Errata policy:** Any future mathematical correction, citation update, or computational refinement is recorded transparently in [`ERRATA.md`](../ERRATA.md) and released as an incremented SemVer tag (`v1.0.1`, etc.) without rewriting prior release tags or git history.
