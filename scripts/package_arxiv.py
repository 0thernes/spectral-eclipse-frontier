#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Build a byte-reproducible standalone arXiv tarball and clean-room compile-verify it."""
from __future__ import annotations

import gzip
import io
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
DIST = ROOT / "dist"
DIST.mkdir(exist_ok=True)
TARBALL = DIST / "arxiv_submission.tar.gz"


def main() -> int:
    # Step 1: compile with --keep-intermediates to generate main.bbl deterministically
    proc = subprocess.run(
        ["tectonic", "-X", "compile", "main.tex", "--keep-intermediates"],
        cwd=PAPER,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        print("ERROR: tectonic compile failed:\n" + proc.stdout + proc.stderr, file=sys.stderr)
        return 1

    shutil.copy2(PAPER / "main.pdf", DIST / "Donahue_2026_spectral_eclipse_frontier.pdf")

    # Step 2: collect exact files for arXiv (main.tex, refs.bib, main.bbl, figures/*.pdf)
    files: list[tuple[Path, str]] = [
        (PAPER / "main.tex", "main.tex"),
        (PAPER / "refs.bib", "refs.bib"),
        (PAPER / "main.bbl", "main.bbl"),
    ]
    for fig in sorted((PAPER / "figures").glob("*.pdf")):
        files.append((fig, f"figures/{fig.name}"))

    for src, _arc in files:
        if not src.is_file():
            print(f"ERROR: missing required arXiv file {src}", file=sys.stderr)
            return 1

    # Byte-reproducible tar.gz (fixed mtime=0, uid=0, gid=0, sorted)
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w") as tf:
        for src, arcname in files:
            data = src.read_bytes()
            if arcname.endswith((".tex", ".bib", ".bbl")):
                data = data.replace(b"\r\n", b"\n")
            ti = tarfile.TarInfo(name=arcname)
            ti.size = len(data)
            ti.mtime = 0
            ti.uid = 0
            ti.gid = 0
            ti.uname = ""
            ti.gname = ""
            ti.mode = 0o644
            tf.addfile(ti, io.BytesIO(data))

    with TARBALL.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
        gz.write(buf.getvalue())

    # Remove intermediate LaTeX scratch files from paper/ to keep repo clean
    for ext in (".aux", ".bbl", ".blg", ".log", ".out", ".toc"):
        p = PAPER / f"main{ext}"
        if p.exists():
            p.unlink()

    # Step 3: Clean-room extract & compile-verify standalone arXiv tarball
    with tempfile.TemporaryDirectory(prefix="se_arxiv_clean_") as tmp:
        with tarfile.open(TARBALL, "r:gz") as tf:
            tf.extractall(tmp)
        chk = subprocess.run(
            ["tectonic", "-X", "compile", "main.tex"],
            cwd=tmp,
            check=False,
            capture_output=True,
            text=True,
        )
        if chk.returncode != 0 or not (Path(tmp) / "main.pdf").is_file():
            print("ERROR: clean-room arXiv tarball compile failed:\n" + chk.stdout + chk.stderr, file=sys.stderr)
            return 1

    print(f"PASS: Built & clean-room compile-verified {TARBALL} ({TARBALL.stat().st_size} bytes, {len(files)} files).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
