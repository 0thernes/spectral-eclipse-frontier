# Security Policy

## Supported Versions

| Version | Supported |
|---|---|
| `1.x` (`v1.1.0` latest) | Yes |

## Reporting a Vulnerability

This repository contains Lean 4 formal proofs, standalone native/WASM scientific computation engines, static GitHub Pages assets, and an AMS-LaTeX manuscript. It runs no network servers, stores no user credentials, and collects no personal data.

If you discover a security vulnerability (for example, memory safety defect in the C/C++/Assembly engines, build-script injection, dependency CVE, or Pages CSP bypass):
- Report privately via GitHub Private Vulnerability Reporting (Security Advisories) on `0thernes/spectral-eclipse-frontier`, or email `0_0@0thernes.art`.
- Please include reproduction steps, affected file/commit SHA, and platform details.
- You can expect an initial acknowledgment within 72 hours and a documented remediation or disclosure timeline.

See `docs/threat-model.md` for the full attack-surface analysis (including proof-kernel integrity and supply-chain verification).
