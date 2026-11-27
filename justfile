# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
# Command runner recipes for Spectral Eclipse Frontier

set shell := ["bash", "-euo", "pipefail", "-c"]

# Build and verify all 10 Lean 4.35.0 theorems + Palomar bridge + 568-theorem axiom audit
lean-verify:
    cd lean && lake exe cache get && lake build SpectralEclipse Challenge Solution VerifyAxioms
    cd lean && lake env lean VerifyAxioms.lean
    python3 scripts/test_lean_negative.py
    python3 scripts/check_readme_axioms.py --require-exhaustive

# Run the full Python verification ladder, linters, typecheck, and 100% B13 mutation audit
test:
    python3 -m pytest -v tests/
    python3 reference/exact_oracle.py
    python3 examples/quickstart.py
    python3 scripts/mutation_audit.py
    ruff check python reference scripts tests
    mypy --strict --explicit-package-bases --ignore-missing-imports python/spectral_eclipse reference/exact_oracle.py scripts/check_readme_axioms.py scripts/mutation_audit.py scripts/test_lean_negative.py scripts/analyze_qrng_study.py scripts/run_polyglot_parity.py scripts/check_citations.py

# Build and cross-verify all 8 polyglot & quantum engines
parity:
    make -C engines/c clean all
    make -C engines/cpp clean all
    cd engines/rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo build --release
    make -C engines/qgtl_qrng clean all
    python3 scripts/run_polyglot_parity.py

# Generate figures, compile frozen PDF + standalone arXiv tarball, and assemble GitHub Pages site
paper:
    python3 scripts/check_citations.py
    python3 scripts/generate_figures.py
    python3 scripts/package_arxiv.py
    python3 scripts/build_blueprint.py
    python3 scripts/build_site.py

# Verify cryptographic SHA-256 manifest and RFC 3161 + OpenTimestamps proofs
verify-integrity:
    python3 scripts/generate_manifest.py --verify
    python3 scripts/stamp_timestamps.py --verify
    bash scripts/audit-repo.sh .

# Full end-to-end reproduction pipeline
reproduce: lean-verify test parity paper verify-integrity
