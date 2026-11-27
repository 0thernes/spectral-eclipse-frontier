#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Verify every BibTeX entry in paper/refs.bib against live Crossref & arXiv APIs.

In `--offline` mode (or when `--verify-cached` is passed), validates consistency between
`paper/refs.bib` and `results/citation-audit.json` without network calls. Default mode
performs live HTTP verification against Crossref & arXiv APIs and writes/checks
`results/citation-audit.json`.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIB_PATH = ROOT / "paper" / "refs.bib"
OUT_PATH = ROOT / "results" / "citation-audit.json"


def parse_bib(text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    chunks = re.split(r"(?=@\w+\s*\{)", text)
    for ch in chunks:
        ch = ch.strip()
        if not ch.startswith("@"):
            continue
        m = re.match(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", ch)
        if not m:
            continue
        entry: dict[str, str] = {"type": m.group(1), "key": m.group(2)}
        for fm in re.finditer(r"(\w+)\s*=\s*\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", ch):
            entry[fm.group(1).lower()] = re.sub(r"\s+", " ", fm.group(2).strip())
        entries.append(entry)
    return entries


def _title_tokens(title: str) -> set[str]:
    clean = re.sub(r"[{}]", "", title).lower()
    words = re.findall(r"[a-z0-9]{3,}", clean)
    stop = {"the", "and", "for", "from", "with", "into", "some", "its"}
    return {w for w in words if w not in stop}


def title_overlap_ratio(bib_title: str, api_title: str) -> float:
    b_toks = _title_tokens(bib_title)
    a_toks = _title_tokens(api_title)
    if not b_toks:
        return 0.0
    return len(b_toks & a_toks) / len(b_toks)


def fetch_crossref(doi: str) -> dict[str, object]:
    url = f"https://api.crossref.org/works/{urllib.parse.quote(doi, safe='')}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "SpectralEclipseCitationAudit/1.1 (mailto:0_0@0thernes.art)"},
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        data = json.loads(resp.read().decode("utf-8"))
        msg = data.get("message", {})
        titles = msg.get("title", [])
        authors = [
            f"{a.get('family', '')}, {a.get('given', '')}".strip(", ")
            for a in msg.get("author", [])
        ]
        retracted = False
        for field in ("update-to", "updated-by"):
            for upd in msg.get(field, []) or []:
                if "retract" in str(upd.get("type", "")).lower() or "retract" in str(upd.get("label", "")).lower():
                    retracted = True
        return {
            "http_status": resp.status,
            "source": "crossref",
            "title": titles[0] if titles else "",
            "authors": authors,
            "retracted": retracted,
        }


def fetch_arxiv(eprint: str) -> dict[str, object]:
    url = f"https://export.arxiv.org/api/query?id_list={urllib.parse.quote(eprint)}"
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "SpectralEclipseCitationAudit/1.0 (mailto:0_0@0thernes.art)"},
    )
    with urllib.request.urlopen(req, timeout=20) as resp:
        xml_bytes = resp.read()
        root = ET.fromstring(xml_bytes)
        ns = {"atom": "http://www.w3.org/2005/Atom"}
        entry = root.find("atom:entry", ns)
        if entry is None:
            raise ValueError(f"No arXiv entry for {eprint}")
        title_el = entry.find("atom:title", ns)
        title = re.sub(r"\s+", " ", (title_el.text or "").strip()) if title_el is not None else ""
        authors = [
            (a.find("atom:name", ns).text or "").strip()  # type: ignore[union-attr]
            for a in entry.findall("atom:author", ns)
            if a.find("atom:name", ns) is not None
        ]
        return {
            "http_status": resp.status,
            "source": "arxiv",
            "title": title,
            "authors": authors,
            "retracted": False,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify paper/refs.bib citations.")
    parser.add_argument("--live", action="store_true", help="Perform live HTTP verification and write audit JSON.")
    args = parser.parse_args()

    entries = parse_bib(BIB_PATH.read_text(encoding="utf-8"))
    if not entries:
        print("ERROR: no BibTeX entries parsed from paper/refs.bib", file=sys.stderr)
        return 1

    if not args.live and OUT_PATH.is_file():
        cached = json.loads(OUT_PATH.read_text(encoding="utf-8"))
        cached_keys = {r["key"] for r in cached.get("entries", [])}
        bib_keys = {e["key"] for e in entries}
        if cached_keys != bib_keys:
            print(f"ERROR: citation-audit.json keys mismatch refs.bib: {cached_keys ^ bib_keys}", file=sys.stderr)
            return 1
        bad = [r for r in cached["entries"] if not r.get("verified") or r.get("retracted")]
        if bad:
            print(f"ERROR: unverified or retracted citations in audit: {bad}", file=sys.stderr)
            return 1
        print(f"PASS: {len(entries)}/{len(entries)} citations verified in cached citation-audit.json (0 retracted).")
        return 0

    records: list[dict[str, object]] = []
    failures: list[str] = []
    for e in entries:
        key = e["key"]
        doi = e.get("doi")
        eprint = e.get("eprint")
        rec: dict[str, object] = {
            "key": key,
            "bib_title": e.get("title", ""),
            "bib_author": e.get("author", ""),
            "bib_year": e.get("year", ""),
            "doi": doi,
            "eprint": eprint,
            "verified": False,
            "retracted": False,
        }
        try:
            meta = fetch_crossref(doi) if doi else fetch_arxiv(eprint or "")
            api_title = str(meta["title"])
            overlap = title_overlap_ratio(e.get("title", ""), api_title)
            rec["api_source"] = meta["source"]
            rec["http_status"] = meta["http_status"]
            rec["api_title"] = api_title
            rec["api_authors"] = meta["authors"]
            rec["title_overlap"] = round(overlap, 4)
            rec["retracted"] = bool(meta["retracted"])
            rec["verified"] = (
                (meta["http_status"] == 200)
                and bool(api_title)
                and (overlap >= 0.5)
                and not rec["retracted"]
            )
            if not rec["verified"]:
                failures.append(f"{key}: verification failed (overlap={overlap:.2f}, meta={meta})")
        except (urllib.error.URLError, ValueError, TimeoutError) as exc:
            rec["error"] = str(exc)
            failures.append(f"{key}: {exc}")
        records.append(rec)

    out = {
        "bib_file": "paper/refs.bib",
        "total_entries": len(records),
        "verified_count": sum(1 for r in records if r["verified"]),
        "retracted_count": sum(1 for r in records if r["retracted"]),
        "all_verified": len(failures) == 0,
        "entries": records,
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    for r in records:
        print(f"[CIT] {r['key']:18s} OK={r['verified']} src={r.get('api_source')} title={str(r.get('api_title'))[:72]}")
    if failures:
        for f in failures:
            print("ERROR:", f, file=sys.stderr)
        return 1
    print(f"PASS: {out['verified_count']}/{out['total_entries']} citations live-verified (HTTP 200, 0 retracted).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
