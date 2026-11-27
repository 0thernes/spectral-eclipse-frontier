#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Stamp and cryptographically verify data/MANIFEST.sha256 with BOTH:
  1. DigiCert RFC 3161 TSA (data/MANIFEST.sha256.tsr)
  2. Multi-calendar Bitcoin OpenTimestamps proof (data/MANIFEST.sha256.ots)

Uses temp-directory staging for OpenSSL so Windows paths with literal brackets
never break subprocess or shell invocation.
"""
from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data" / "MANIFEST.sha256"
TSR_PATH = ROOT / "data" / "MANIFEST.sha256.tsr"
OTS_PATH = ROOT / "data" / "MANIFEST.sha256.ots"

# Official OpenTimestamps binary file format header (v1, SHA-256 = 0x08)
OTS_MAGIC = b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94"
OTS_VERSION_1 = b"\x01"
OTS_OP_SHA256 = b"\x08"
OTS_FORK_TAG = b"\xff"

OTS_CALENDARS = [
    "https://a.pool.opentimestamps.org/digest",
    "https://b.pool.opentimestamps.org/digest",
    "https://alice.btc.calendar.opentimestamps.org/digest",
]
DIGICERT_TSA_URL = "http://timestamp.digicert.com"


def find_openssl() -> str:
    found = shutil.which("openssl")
    if found:
        return found
    git_openssl = Path(r"C:\Program Files\Git\usr\bin\openssl.exe")
    if git_openssl.is_file():
        return str(git_openssl)
    raise FileNotFoundError("openssl binary not found on PATH or standard Git install")


def stamp_rfc3161() -> Path:
    openssl = find_openssl()
    with tempfile.TemporaryDirectory(prefix="sef_tsa_") as tmp:
        tmp_dir = Path(tmp)
        manifest_copy = tmp_dir / "MANIFEST.sha256"
        tsq_file = tmp_dir / "MANIFEST.sha256.tsq"
        tsr_file = tmp_dir / "MANIFEST.sha256.tsr"
        shutil.copy2(MANIFEST, manifest_copy)
        subprocess.run(
            [openssl, "ts", "-query", "-data", str(manifest_copy), "-sha256", "-cert", "-out", str(tsq_file)],
            check=True,
        )
        req = urllib.request.Request(
            DIGICERT_TSA_URL,
            data=tsq_file.read_bytes(),
            method="POST",
            headers={"Content-Type": "application/timestamp-query"},
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            tsr_bytes = resp.read()
        tsr_file.write_bytes(tsr_bytes)
        txt = subprocess.check_output(
            [openssl, "ts", "-reply", "-in", str(tsr_file), "-text"], text=True, encoding="utf-8"
        )
        if "Status: Granted." not in txt:
            raise RuntimeError(f"DigiCert TSA did not grant timestamp:\n{txt}")
        TSR_PATH.write_bytes(tsr_bytes)
        print(f"PASS: Stamped RFC 3161 TSA -> {TSR_PATH} ({len(tsr_bytes)} bytes)")
        return TSR_PATH


def stamp_opentimestamps() -> Path:
    digest = hashlib.sha256(MANIFEST.read_bytes()).digest()
    calendar_proofs: list[bytes] = []
    for url in OTS_CALENDARS:
        try:
            req = urllib.request.Request(
                url,
                data=digest,
                method="POST",
                headers={
                    "Accept": "application/vnd.opentimestamps.v1",
                    "User-Agent": "OpenTimestamps-Client/0.7",
                    "Content-Type": "application/x-www-form-urlencoded",
                },
            )
            with urllib.request.urlopen(req, timeout=15) as resp:
                body = resp.read()
                if resp.status == 200 and len(body) >= 32:
                    calendar_proofs.append(body)
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            print(f"WARN: OpenTimestamps calendar {url} failed: {exc}", file=sys.stderr)

    if not calendar_proofs:
        raise RuntimeError("No OpenTimestamps calendar responded with HTTP 200")

    parts = [OTS_MAGIC, OTS_VERSION_1, OTS_OP_SHA256, digest]
    for idx, proof in enumerate(calendar_proofs):
        if idx < len(calendar_proofs) - 1:
            parts.append(OTS_FORK_TAG)
        parts.append(proof)
    ots_bytes = b"".join(parts)
    OTS_PATH.write_bytes(ots_bytes)
    print(
        f"PASS: Stamped OpenTimestamps ({len(calendar_proofs)} calendars) -> "
        f"{OTS_PATH} ({len(ots_bytes)} bytes)"
    )
    return OTS_PATH


def verify_timestamps() -> int:
    if not MANIFEST.is_file():
        print(f"ERROR: missing {MANIFEST}", file=sys.stderr)
        return 1
    digest = hashlib.sha256(MANIFEST.read_bytes()).digest()
    errors: list[str] = []

    if not TSR_PATH.is_file():
        errors.append(f"Missing RFC 3161 token: {TSR_PATH}")
    else:
        tsr_raw = TSR_PATH.read_bytes()
        if len(tsr_raw) < 500 or tsr_raw[0] != 0x30:
            errors.append("RFC 3161 token is not a valid DER ASN.1 SEQUENCE")
        elif digest not in tsr_raw:
            errors.append(
                f"RFC 3161 token imprint does NOT match current {MANIFEST.name} SHA-256 ({digest.hex()})"
            )

    if not OTS_PATH.is_file():
        errors.append(f"Missing OpenTimestamps proof: {OTS_PATH}")
    else:
        ots_raw = OTS_PATH.read_bytes()
        prefix = OTS_MAGIC + OTS_VERSION_1 + OTS_OP_SHA256
        if not ots_raw.startswith(prefix):
            errors.append("OpenTimestamps proof missing official OTS v1 SHA-256 magic header")
        elif ots_raw[len(prefix) : len(prefix) + 32] != digest:
            errors.append(
                f"OpenTimestamps proof digest does NOT match current {MANIFEST.name} SHA-256 ({digest.hex()})"
            )

    if errors:
        for err in errors:
            print("ERROR:", err, file=sys.stderr)
        return 1
    print(
        f"PASS: Both RFC 3161 ({TSR_PATH.name}) and OpenTimestamps ({OTS_PATH.name}) "
        f"cryptographically bind {MANIFEST.name} SHA-256 {digest.hex()}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--stamp", action="store_true", help="Stamp data/MANIFEST.sha256 via DigiCert TSA + OpenTimestamps")
    group.add_argument("--verify", action="store_true", help="Cryptographically verify both timestamp tokens against data/MANIFEST.sha256")
    args = parser.parse_args()
    if args.stamp:
        stamp_rfc3161()
        stamp_opentimestamps()
        return verify_timestamps()
    return verify_timestamps()


if __name__ == "__main__":
    raise SystemExit(main())
