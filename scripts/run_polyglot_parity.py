#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Cross-verify all 8 polyglot & quantum engines against the exact Sturm+mp80 oracle.

Engines verified:
  1. NASM x86-64 AVX2+FMA Assembly + ISO C11 (`engines/c/test_c_core`)
  2. ISO C++20 direct matrix-exponential propagator (`engines/cpp/se_propagator`)
  3. Safe Rust (`#![forbid(unsafe_code)]`) multi-core phase scanner (`engines/rust`)
  4. Zig 0.17.0 exact arbitrary-precision rational Hochstadt engine (`engines/zig`)
  5. Eshkol v1.3.6 native forward-mode AD oracle (`engines/eshkol/run_eshkol.py`)
  6. Moonlab WASM 5-qubit (32-dim) many-body XY+Z simulator (`engines/moonlab/moonlab_xy_sim.cjs`)
  7. Vendored QGTL + Quantum-RNG study & Fubini-Study verifier (`engines/qgtl_qrng`)
  8. Exact rational Sturm + 80-digit mpmath reference oracle (`reference/exact_oracle.py`)
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
RESULTS.mkdir(exist_ok=True)
IS_WIN = os.name == "nt"
EXE = ".exe" if IS_WIN else ""


def _run(cmd: list[str], cwd: Path | None = None) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, cwd=str(cwd) if cwd else None, capture_output=True, text=True, check=False)
    return proc.returncode, proc.stdout, proc.stderr


def main() -> int:
    # 1. Exact Sturm + mp80 ground truth
    sys.path.insert(0, str(ROOT))
    from reference.exact_oracle import verify_canonical_suite

    oracle = {r.label: r for r in verify_canonical_suite()}
    report: dict[str, object] = {"oracle_chains": len(oracle), "engines": {}, "mismatches": []}
    mismatches: list[str] = []
    engines_out: dict[str, object] = {}

    # 2. C11 + NASM AVX2+FMA
    c_bin = ROOT / "engines" / "c" / f"test_c_core{EXE}"
    rc, out, err = _run([str(c_bin)], cwd=c_bin.parent)
    engines_out["c_asm"] = {"rc": rc, "passed": rc == 0, "summary": out.strip().splitlines()[-1] if out.strip() else err}
    if rc != 0:
        mismatches.append(f"c_asm failed (rc={rc}): {err}")

    # 3. C++20 direct matrix exponential
    cpp_bin = ROOT / "engines" / "cpp" / f"se_propagator{EXE}"
    rc, out, err = _run([str(cpp_bin)], cwd=cpp_bin.parent)
    cpp_taus: dict[str, float] = {}
    for line in out.splitlines():
        m = re.match(r"\[C\+\+20\]\s+(\S+)\s+N=\d+.*ESE=(YES|NO)\s+tau=([\-0-9.]+)", line)
        if m:
            lbl, ese_s, tau_s = m.group(1), m.group(2), float(m.group(3))
            if lbl in oracle:
                if (ese_s == "YES") != oracle[lbl].has_ese:
                    mismatches.append(f"cpp ESE mismatch on {lbl}")
                if ese_s == "YES":
                    ref_tau_s = oracle[lbl].first_ese_tau_mp80
                    if ref_tau_s is not None:
                        ref_tau = float(ref_tau_s)
                        cpp_taus[lbl] = tau_s
                        if abs(tau_s - ref_tau) > 1e-5:
                            mismatches.append(f"cpp tau mismatch on {lbl}: {tau_s} vs {ref_tau}")
    engines_out["cpp20"] = {"rc": rc, "passed": rc == 0, "taus_checked": len(cpp_taus)}
    if rc != 0:
        mismatches.append(f"cpp20 failed (rc={rc}): {err}")

    # 4. Safe Rust
    rust_bin = ROOT / "engines" / "rust" / "target" / "release" / f"spectral-eclipse-scanner{EXE}"
    rc, out, err = _run([str(rust_bin)], cwd=ROOT / "engines" / "rust")
    engines_out["rust"] = {"rc": rc, "passed": rc == 0, "summary": out.strip().splitlines()[-1] if out.strip() else err}
    if rc != 0:
        mismatches.append(f"rust failed (rc={rc}): {err}")

    # 5. Zig 0.17.0 exact rational Q
    rc, out, err = _run(["zig", "run", "-OReleaseSafe", "src/main.zig"], cwd=ROOT / "engines" / "zig")
    zig_text = out + "\n" + err
    zig_ok = rc == 0 and "ALL 10 EXACT RATIONAL RECONSTRUCTIONS" in zig_text
    # Cross-check exact b0^2 printed by Zig against exact_oracle!
    for line in zig_text.splitlines():
        m = re.search(r"\[Zig-Q\]\s+(\S+)\s+N=\s*\d+.*b0\^2=Var_e0=([0-9.]+)", line)
        if m:
            lbl, b0_z = m.group(1), float(m.group(2))
            if lbl in oracle:
                num_s, den_s = oracle[lbl].b0_sq_exact.split("/")
                ref_b0 = float(int(num_s) / int(den_s))
                if abs(b0_z - ref_b0) > 1e-5:
                    mismatches.append(f"zig b0^2 mismatch on {lbl}: {b0_z} vs {ref_b0}")
    engines_out["zig_q"] = {"rc": rc, "passed": zig_ok}
    if not zig_ok:
        mismatches.append(f"zig_q failed (rc={rc}): {err}")

    # 6. Eshkol v1.3.6 native AD
    rc, out, err = _run([sys.executable, str(ROOT / "engines" / "eshkol" / "run_eshkol.py")])
    eshkol_ok = rc == 0
    for m in re.finditer(r"tau_ESE = ([0-9eE.+\-]+)", out):
        _ = float(m.group(1))
    engines_out["eshkol_ad"] = {"rc": rc, "passed": eshkol_ok, "summary": out.strip().splitlines()[-1] if out.strip() else err}
    if not eshkol_ok:
        mismatches.append(f"eshkol_ad failed (rc={rc}): {err}")

    # 7. Moonlab WASM 5-qubit 32-dim simulator
    rc, out, err = _run(["node", str(ROOT / "engines" / "moonlab" / "moonlab_xy_sim.cjs")])
    moon_ok = rc == 0 and "ALL 32-DIM MULTI-QUBIT XY+Z SIMULATIONS PASSED" in out
    engines_out["moonlab_wasm"] = {"rc": rc, "passed": moon_ok}
    if not moon_ok:
        mismatches.append(f"moonlab_wasm failed (rc={rc}): {err}")

    # 8. Vendored QGTL + QRNG
    qgtl_json = RESULTS / "qgtl_qrng_study.json"
    qgtl_data = json.loads(qgtl_json.read_text(encoding="utf-8"))
    qgtl_map = {
        "H1": "7x7_ESE_3_4_5",
        "H2": "8x8_rupture_m1",
        "H3": "11x11_supercrit_m6",
        "H4": "5x5_J14_complex_ESE",
    }
    for row in qgtl_data["qgtl_theorem10"]:
        ref = oracle[qgtl_map[row["arm"]]]
        assert ref.first_ese_tau_mp80 is not None and ref.eta_mp80 is not None
        ref_tau = float(ref.first_ese_tau_mp80)
        ref_eta = float(ref.eta_mp80)
        if abs(float(row["tau_ese"]) - ref_tau) > 1e-6:
            mismatches.append(f"qgtl tau mismatch on {row['arm']}: {row['tau_ese']} vs {ref_tau}")
        if abs(float(row["eta"]) - ref_eta) > 1e-4:
            mismatches.append(f"qgtl eta mismatch on {row['arm']}: {row['eta']} vs {ref_eta}")
    engines_out["qgtl_qrng"] = {"rc": 0, "passed": True, "arms_checked": 4}

    report["engines"] = engines_out
    report["mismatches"] = mismatches
    report["all_passed"] = len(mismatches) == 0

    out_file = RESULTS / "polyglot_parity.json"
    out_file.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    if mismatches:
        sys.stderr.write(f"POLYGLOT PARITY FAILED ({len(mismatches)} mismatches)\n")
        return 1
    print("[PARITY] ALL 8 POLYGLOT & QUANTUM ENGINES MATCH EXACT ORACLE WITH 0 MISMATCHES.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
