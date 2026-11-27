#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Run the Eshkol v1.3.6 native AD oracle and verify dual-number parity."""

from __future__ import annotations

import json
import math
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ESK_FILE = HERE / "ese_ad_oracle.esk"
DEFAULT_WIN_ESHKOL = Path(r"Z:\Tools\eshkol\eshkol-v1.3.6-evolve-windows-x64-cuda\bin\eshkol-run.exe")


class Dual:
    """Minimal exact forward-mode dual number a + b*eps (eps^2 = 0) for CI parity check."""

    __slots__ = ("v", "d")

    def __init__(self, v: float, d: float = 0.0) -> None:
        self.v = float(v)
        self.d = float(d)

    def __add__(self, o: Dual | float) -> Dual:
        o = o if isinstance(o, Dual) else Dual(o)
        return Dual(self.v + o.v, self.d + o.d)

    def __radd__(self, o: float) -> Dual:
        return Dual(o + self.v, self.d)

    def __sub__(self, o: Dual | float) -> Dual:
        o = o if isinstance(o, Dual) else Dual(o)
        return Dual(self.v - o.v, self.d - o.d)

    def __rsub__(self, o: float) -> Dual:
        return Dual(o - self.v, -self.d)

    def __mul__(self, o: Dual | float) -> Dual:
        o = o if isinstance(o, Dual) else Dual(o)
        return Dual(self.v * o.v, self.d * o.v + self.v * o.d)

    def __rmul__(self, o: float) -> Dual:
        return Dual(o * self.v, o * self.d)

    def __truediv__(self, o: Dual | float) -> Dual:
        o = o if isinstance(o, Dual) else Dual(o)
        return Dual(self.v / o.v, (self.d * o.v - self.v * o.d) / (o.v * o.v))

    def cos(self) -> Dual:
        return Dual(math.cos(self.v), -math.sin(self.v) * self.d)


def _eval_weighted_cos(weights: list[float], freqs: list[float], t: float) -> tuple[float, float]:
    dt = Dual(t, 1.0)
    num = Dual(0.0, 0.0)
    den = sum(weights)
    for w, f in zip(weights, freqs):
        num = num + (dt * f).cos() * w
    res = num / den
    return res.v, res.d


def _newton_dual(weights: list[float], freqs: list[float], x0: float, steps: int = 12) -> tuple[float, float, float]:
    t = x0
    for _ in range(steps):
        v, d = _eval_weighted_cos(weights, freqs, t)
        t -= v / d
    v, d = _eval_weighted_cos(weights, freqs, t)
    return t, v, d


def reference_dual_results() -> dict[str, dict[str, float]]:
    t7, a7, d7 = _newton_dual([7.0, 25.0, 25.0, 7.0], [0.0, 3.0, 4.0, 5.0], 0.45)
    t8, a8, d8 = _newton_dual(
        [1.0 / 460800.0, 1.0 / 774144.0, 1.0 / 921600.0, 1.0 / 3801600.0],
        [0.5, 3.5, 4.5, 5.5],
        0.60,
    )
    w11 = [
        1.0 / (144.0 * 169.0 * 196.0 * 225.0),
        1.0 / (143.0 * 168.0 * 195.0 * 224.0),
        1.0 / (144.0 * 143.0 * 25.0 * 52.0 * 81.0),
        1.0 / (169.0 * 168.0 * 25.0 * 27.0 * 56.0),
        1.0 / (196.0 * 195.0 * 52.0 * 27.0 * 29.0),
        1.0 / (225.0 * 224.0 * 81.0 * 56.0 * 29.0),
    ]
    t11, a11, d11 = _newton_dual(w11, [0.0, 1.0, 12.0, 13.0, 14.0, 15.0], 0.20)
    return {
        "7x7_345": {"tau": t7, "amp": a7, "deriv": d7},
        "8x8_m1": {"tau": t8, "amp": a8, "deriv": d8},
        "11x11_m6": {"tau": t11, "amp": a11, "deriv": d11},
    }


def find_eshkol_bin() -> str | None:
    env_bin = os.environ.get("ESHKOL_BIN")
    if env_bin and Path(env_bin).is_file():
        return env_bin
    on_path = shutil.which("eshkol-run")
    if on_path:
        return on_path
    if DEFAULT_WIN_ESHKOL.is_file():
        return str(DEFAULT_WIN_ESHKOL)
    return None


def main() -> int:
    ref = reference_dual_results()
    eshkol_bin = find_eshkol_bin()
    payload: dict[str, object] = {
        "mode": "dual_reference_fallback",
        "eshkol_bin": eshkol_bin,
        "reference_dual": ref,
    }
    if eshkol_bin:
        proc = subprocess.run(
            [eshkol_bin, "-r", str(ESK_FILE)],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            sys.stderr.write(proc.stderr)
            return proc.returncode
        out = proc.stdout.strip()
        print(out)
        nums = re.findall(r"tau_ESE = ([0-9eE.+\-]+)\s+A\(tau\) = ([0-9eE.+\-]+)\s+A'\(tau\) = ([0-9eE.+\-]+)", out)
        if len(nums) != 3:
            sys.stderr.write("Failed to parse 3 Eshkol AD root lines\n")
            return 2
        keys = ["7x7_345", "8x8_m1", "11x11_m6"]
        max_diff = 0.0
        eshkol_parsed = {}
        for k, (tau_s, amp_s, d_s) in zip(keys, nums):
            tau_v, amp_v, d_v = float(tau_s), float(amp_s), float(d_s)
            eshkol_parsed[k] = {"tau": tau_v, "amp": amp_v, "deriv": d_v}
            max_diff = max(max_diff, abs(tau_v - ref[k]["tau"]), abs(d_v - ref[k]["deriv"]))
        if max_diff > 1e-12:
            sys.stderr.write(f"Eshkol AD vs dual parity failed: max_diff={max_diff}\n")
            return 3
        payload["mode"] = "native_eshkol_v1.3.6_ad"
        payload["eshkol_native"] = eshkol_parsed
        payload["max_parity_diff"] = max_diff
        print(f"[Eshkol AD] Native Eshkol v1.3.6 vs Dual parity max_diff = {max_diff:.3e} PASS")
    else:
        print("[Eshkol AD] eshkol-run binary not on PATH; ran pure dual-number reference parity check.")
        print(json.dumps(ref, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
