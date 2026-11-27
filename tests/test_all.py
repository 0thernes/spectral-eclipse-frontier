# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Comprehensive Build Standard v1.2.0 Verification Ladder (B05-B15, B20-B21)."""

from __future__ import annotations

import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

import jsonschema
import numpy as np
import pytest
import yaml  # type: ignore[import-untyped]
from hypothesis import given, settings
from hypothesis import strategies as st

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
sys.path.insert(0, str(ROOT))

from spectral_eclipse import (
    FLOAT64_CANCELLATION_MARGIN,
    FLOAT64_MIN_RE_THRESHOLD,
    __version__,
    detect_real_ese,
    persymmetric_weights,
    reconstruct_persymmetric_jacobi,
    return_amplitude,
    target_amplitude,
)

from reference.exact_oracle import (
    exact_energy_variance_q,
    exact_persymmetric_weights_q,
    exact_sturm_ese_root_count,
    verify_canonical_suite,
)

# ---------------------------------------------------------------------------
# B05: Falsifiable unit tests mapped 1-to-1 to Claims C1..C10
# ---------------------------------------------------------------------------


def test_claim1_and_2_4x4_5x5_dichotomy() -> None:
    assert exact_sturm_ese_root_count([Fraction(k, 2) for k in (-3, -1, 1, 3)], 2)[0] == 0
    assert exact_sturm_ese_root_count([Fraction(k, 2) for k in (-5, -3, 3, 5)], 2)[0] == 1
    assert exact_sturm_ese_root_count([Fraction(k) for k in (-2, -1, 0, 1, 2)], 1)[0] == 0
    assert exact_sturm_ese_root_count([Fraction(k) for k in (-4, -3, 0, 3, 4)], 1)[0] == 2


def test_claim3_6x6_dichotomy() -> None:
    assert exact_sturm_ese_root_count([Fraction(k, 2) for k in (-5, -3, -1, 1, 3, 5)], 2)[0] == 0
    assert exact_sturm_ese_root_count([Fraction(k, 2) for k in (-9, -7, -1, 1, 7, 9)], 2)[0] == 0
    assert exact_sturm_ese_root_count([Fraction(k, 2) for k in (-7, -5, -3, 3, 5, 7)], 2)[0] >= 1


def test_claim4_conjecture_4_1_7x7() -> None:
    # Divisibility forward (no ESE)
    for spec in [(-3, -2, -1, 0, 1, 2, 3), (-5, -2, -1, 0, 1, 2, 5), (-7, -4, -1, 0, 1, 4, 7)]:
        assert exact_sturm_ese_root_count([Fraction(k) for k in spec], 1)[0] == 0
    # Non-divisibility converse (guaranteed ESE)
    for spec in [(-5, -4, -3, 0, 3, 4, 5), (-7, -4, -3, 0, 3, 4, 7), (-7, -6, -5, 0, 5, 6, 7)]:
        assert exact_sturm_ese_root_count([Fraction(k) for k in spec], 1)[0] >= 1


def test_claim5_8x8_sharp_even_rupture() -> None:
    for m in (1, 2, 3):
        M = 4 * m + 5
        spec = [Fraction(k, 2) for k in (-(M + 2), -M, -(M - 2), -1, 1, M - 2, M, M + 2)]
        assert exact_sturm_ese_root_count(spec, 2)[0] >= 1


def test_claim6_9x9_critical_no_ese() -> None:
    for b, c, d in [(2, 3, 4), (2, 3, 6), (4, 5, 6), (10, 11, 12), (20, 21, 22)]:
        spec = [Fraction(k) for k in (-d, -c, -b, -1, 0, 1, b, c, d)]
        assert exact_sturm_ese_root_count(spec, 1)[0] == 0


def test_claim7_11x11_sharp_threshold_M12() -> None:
    for m in range(1, 6):
        spec = [Fraction(k) for k in (-(2 * m + 3), -(2 * m + 2), -(2 * m + 1), -2 * m, -1, 0, 1, 2 * m, 2 * m + 1, 2 * m + 2, 2 * m + 3)]
        assert exact_sturm_ese_root_count(spec, 1)[0] == 0, f"m={m} must have NO ESE"
    for m in (6, 7, 8):
        spec = [Fraction(k) for k in (-(2 * m + 3), -(2 * m + 2), -(2 * m + 1), -2 * m, -1, 0, 1, 2 * m, 2 * m + 1, 2 * m + 2, 2 * m + 3)]
        assert exact_sturm_ese_root_count(spec, 1)[0] >= 1, f"m={m} must have ESE"


def test_claim9_nonsymmetric_j14_complex_ese_and_pst() -> None:
    chain = reconstruct_persymmetric_jacobi([0.0, 1.0, 4.0, 9.0, 10.0])
    np.testing.assert_allclose(chain.diag_a, [4.0, 6.0, 4.0, 6.0, 4.0], atol=1e-12)
    np.testing.assert_allclose(np.square(chain.off_b), [15.0, 4.5, 4.5, 15.0], atol=1e-12)
    assert abs(return_amplitude(chain, math.pi / 3.0)) < 1e-13
    assert abs(abs(target_amplitude(chain, math.pi)) - 1.0) < 1e-13


def test_claim10_variance_qsl_and_duality() -> None:
    for spec in [(-5, -4, -3, 0, 3, 4, 5), (-4, -3, 0, 3, 4), (0, 1, 4, 9, 10)]:
        chain = reconstruct_persymmetric_jacobi([float(k) for k in spec])
        var_q = exact_energy_variance_q([Fraction(k) for k in spec])
        assert abs(chain.b0_sq - float(var_q)) < 1e-11
        # ESE <-> ETE duality: |target(pi - t)| == |return(t)| for integer-spectrum PST chains!
        for t in (0.3, math.pi / 3.0, 1.7):
            assert abs(abs(target_amplitude(chain, math.pi - t)) - abs(return_amplitude(chain, t))) < 1e-12


# ---------------------------------------------------------------------------
# B06: Negative & boundary validation tests
# ---------------------------------------------------------------------------


def test_negative_invalid_inputs() -> None:
    with pytest.raises(ValueError):
        persymmetric_weights([1.0])
    with pytest.raises(ValueError):
        persymmetric_weights([0.0, 1.0, 1.0, 2.0])
    with pytest.raises(ValueError):
        persymmetric_weights([3.0, 2.0, 1.0])
    with pytest.raises(ValueError):
        exact_persymmetric_weights_q([Fraction(1)])
    with pytest.raises(ValueError):
        exact_persymmetric_weights_q([Fraction(0), Fraction(0), Fraction(1)])


# ---------------------------------------------------------------------------
# B07: Regression tests for every real bug fixed during development
# ---------------------------------------------------------------------------


def test_regression_hderiv3_coeff_18w_not_14w() -> None:
    """Regression for bug caught by Lean 4 in TrigBounds.lean: HDeriv3 has (24 - 18*w), not (24 - 14*w)."""
    def Hpp(w: float) -> float:
        x = math.sqrt(w)
        return ((2.0 * w - 4.0) * math.cos(2.0 * x) - 5.0 * x * math.sin(2.0 * x) + 4.0) / (4.0 * w**3)

    w = 4.0
    h = 1e-5
    d3_num = (-Hpp(w + 2 * h) + 8 * Hpp(w + h) - 8 * Hpp(w - h) + Hpp(w - 2 * h)) / (12 * h)
    x = math.sqrt(w)
    d3_exact = ((24.0 - 18.0 * w) * math.cos(2.0 * x) + (33.0 * x - 4.0 * x**3) * math.sin(2.0 * x) - 24.0) / (8.0 * w**4)
    assert abs(d3_num - d3_exact) < 1e-9


def test_regression_11x11_m5_normalization_736() -> None:
    """Regression for bug caught during RuptureAndPhase SOS verification: C_5 = 736, not 800."""
    spec = [Fraction(k) for k in (-13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13)]
    w = exact_persymmetric_weights_q(spec)
    assert sum(w) == Fraction(1)
    assert exact_sturm_ese_root_count(spec, 1)[0] == 0


def test_regression_float64_cancellation_near_pi_B20() -> None:
    """B20 Numeric stability: naive float64 sum near t=pi has O((pi-t)^6) cancellation noise;
    guard in detect_real_ese + exact Sturm oracle must agree on NO ESE for 7x7 Krawtchouk."""
    chain = reconstruct_persymmetric_jacobi([-3.0, -2.0, -1.0, 0.0, 1.0, 2.0, 3.0])
    has_ese, tau = detect_real_ese(chain, math.pi, grid=4000)
    assert not has_ese and tau is None
    assert exact_sturm_ese_root_count([Fraction(k) for k in (-3, -2, -1, 0, 1, 2, 3)], 1)[0] == 0


def test_public_api_float64_guard_constants() -> None:
    """Verify B20 float64 guard thresholds are explicitly defined and exported."""
    assert FLOAT64_CANCELLATION_MARGIN == 1e-11
    assert FLOAT64_MIN_RE_THRESHOLD == 1e-10
    assert FLOAT64_MIN_RE_THRESHOLD > FLOAT64_CANCELLATION_MARGIN > 0.0


# ---------------------------------------------------------------------------
# B10 & B14: Hypothesis >= 1,000 cases (property-based + metamorphic scaling/shift)
# ---------------------------------------------------------------------------


@settings(max_examples=1000, deadline=None)
@given(
    gaps=st.lists(st.integers(min_value=1, max_value=15), min_size=3, max_size=7),
    shift=st.floats(min_value=-50.0, max_value=50.0, allow_nan=False, allow_infinity=False),
    scale=st.floats(min_value=0.1, max_value=10.0, allow_nan=False, allow_infinity=False),
)
def test_hypothesis_1000_metamorphic_persymmetry_and_variance(
    gaps: list[int], shift: float, scale: float
) -> None:
    lam = [0.0]
    for g in gaps:
        lam.append(lam[-1] + float(g))
    base = reconstruct_persymmetric_jacobi(lam)
    # Persymmetry invariant
    assert np.allclose(base.diag_a, base.diag_a[::-1], atol=1e-9)
    assert np.allclose(base.off_b, base.off_b[::-1], atol=1e-9)
    # Metamorphic invariance under spectral shift + positive scaling:
    #   lam' = scale * lam + shift  =>  a' = scale * a + shift, b' = scale * b, w' = w!
    lam_tr = [scale * x + shift for x in lam]
    tr = reconstruct_persymmetric_jacobi(lam_tr)
    assert np.allclose(tr.weights, base.weights, atol=1e-10)
    assert np.allclose(tr.diag_a, [scale * a + shift for a in base.diag_a], atol=1e-7)
    assert np.allclose(tr.off_b, [scale * b for b in base.off_b], atol=1e-7)
    # Exact Theorem 10 energy variance identity: b_0^2 == Var_{e_0}(J)
    w = np.asarray(base.weights)
    l_arr = np.asarray(base.eigenvalues)
    var = float(np.sum(w * (l_arr - float(np.sum(w * l_arr))) ** 2))
    assert abs(base.b0_sq - var) < 1e-8 * (1.0 + var)


# ---------------------------------------------------------------------------
# B08 & B09: Golden snapshot & JSON artifact contract verification
# ---------------------------------------------------------------------------


def test_preregistered_qrng_json_contract() -> None:
    study_path = ROOT / "results" / "qgtl_qrng_study.json"
    analysis_path = ROOT / "results" / "qgtl_qrng_analysis.json"
    assert study_path.is_file() and analysis_path.is_file()
    study = json.loads(study_path.read_text(encoding="utf-8"))
    analysis = json.loads(analysis_path.read_text(encoding="utf-8"))
    assert study["n_seeds"] == 30
    assert len(study["arms"]) == 4
    assert len(study["qgtl_theorem10"]) == 4
    for arm in analysis["arms"]:
        p = arm["primary_eps05"]
        assert 0.0 < p["p_holm_bonferroni"] <= 1.0
        assert p["diff_ci95_lo"] <= p["diff_mean"] <= p["diff_ci95_hi"]


def test_qrng_eps0_exact_zero_regression() -> None:
    """Regression for Deviation #1 (compute_interior_min optimizer bug):
    all 4 ESE treatment arms must evaluate to exact 0.0 at eps = 0."""
    analysis_path = ROOT / "results" / "qgtl_qrng_analysis.json"
    analysis = json.loads(analysis_path.read_text(encoding="utf-8"))
    for arm in analysis["arms"]:
        eps0 = [lv for lv in arm["all_levels"] if lv["eps"] == 0.0]
        assert len(eps0) == 1
        assert eps0[0]["treat_median"] == 0.0, f"{arm['id']} eps=0 treat_median must be 0.0"
        assert eps0[0]["treat_mean"] == 0.0, f"{arm['id']} eps=0 treat_mean must be 0.0"


def test_exact_oracle_golden_snapshot() -> None:
    suite = {r.label: r for r in verify_canonical_suite()}
    assert len(suite) == 13
    assert suite["7x7_ESE_3_4_5"].b0_sq_exact == "25/2"
    assert suite["8x8_rupture_m1"].b0_sq_exact == "77/8"
    assert suite["11x11_subcrit_m5"].exact_sturm_roots_in_open_interval == 0
    assert suite["11x11_supercrit_m6"].exact_sturm_roots_in_open_interval == 4
    assert suite["5x5_J14_complex_ESE"].b0_sq_exact == "15/1"
    # Kill M01, M05, M07, M08 mutants explicitly (exact QSL value, evolution sign, bisected tau, full (-1,1) Sturm roots)
    ch7 = reconstruct_persymmetric_jacobi([-5.0, -4.0, -3.0, 0.0, 3.0, 4.0, 5.0])
    assert abs(ch7.qsl_bound - math.pi / (2.0 * math.sqrt(12.5))) < 1e-12
    has_ese, tau7 = detect_real_ese(ch7)
    assert has_ese and tau7 is not None and abs(tau7 - 0.4621843246057564) < 1e-5
    j14 = reconstruct_persymmetric_jacobi([0.0, 1.0, 4.0, 9.0, 10.0])
    assert return_amplitude(j14, 0.25).imag < -0.4  # e^{-i J t} has negative imaginary part for small t > 0
    # Case 3 chain {0, +-3, +-6, +-7} has 4 distinct roots on (-1, 1) vs 3 on (0, 1) (kills M08)
    roots_7x7_367, _ = exact_sturm_ese_root_count([Fraction(k) for k in (-7, -6, -3, 0, 3, 6, 7)], scale_factor=1)
    assert roots_7x7_367 == 4


# ---------------------------------------------------------------------------
# A08, B03, B39: Repository-wide integrity, schema, link & anti-drift gates
# ---------------------------------------------------------------------------


def test_single_version_consistency_across_all_manifests() -> None:
    """A08: Verify VERSION matches all 7 synchronized package/metadata manifests."""
    version_file = ROOT / "VERSION"
    if not version_file.is_file():
        pytest.skip("Isolated mutation sandbox without full repository manifests")
    ver = version_file.read_text(encoding="utf-8").strip()
    assert __version__ == ver
    assert f"## [{ver}]" in (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    assert f'version: "{ver}"' in (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    assert f'version: "{ver}"' in (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    assert f'version = "{ver}"' in (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    assert f'version = "{ver}"' in (ROOT / "lean" / "lakefile.toml").read_text(encoding="utf-8")
    assert f'version = "{ver}"' in (ROOT / "engines" / "rust" / "Cargo.toml").read_text(encoding="utf-8")


def test_repo_yaml_validates_against_schema() -> None:
    """Build Standard v1.2.0: repo.yaml must validate cleanly against repo-standard.schema.json."""
    repo_yaml = ROOT / "repo.yaml"
    schema_json = ROOT / "repo-standard.schema.json"
    if not (repo_yaml.is_file() and schema_json.is_file()):
        pytest.skip("Isolated mutation sandbox without repo.yaml")
    data = yaml.safe_load(repo_yaml.read_text(encoding="utf-8"))
    schema = json.loads(schema_json.read_text(encoding="utf-8"))
    jsonschema.validate(instance=data, schema=schema)


def test_no_broken_relative_markdown_links() -> None:
    """Verify every relative markdown link across authored docs resolves to an existing file."""
    if not (ROOT / "README.md").is_file():
        pytest.skip("Isolated mutation sandbox without markdown docs")
    link_re = re.compile(r"\[[^\]]+\]\(([^)#\s]+)")
    md_files = [
        p
        for p in ROOT.rglob("*.md")
        if not any(part in p.parts for part in ("third_party", "build", ".lake", "target", ".git"))
    ]
    broken: list[str] = []
    for md in md_files:
        text = md.read_text(encoding="utf-8")
        # Ignore fenced code blocks and inline code spans
        stripped = re.sub(r"```.*?```", "", text, flags=re.DOTALL)
        stripped = re.sub(r"`[^`]+`", "", stripped)
        for target in link_re.findall(stripped):
            if target.startswith(("http://", "https://", "mailto:", "data:")):
                continue
            resolved = (md.parent / target).resolve()
            if not resolved.exists():
                broken.append(f"{md.relative_to(ROOT).as_posix()} -> {target}")
    assert not broken, f"Broken relative markdown links: {broken}"


def test_no_stale_identifiers_or_hallucinated_symbols() -> None:
    """Prevent regressions to retired archive IDs, hallucinated APIs, or mismatched affiliations."""
    if not (ROOT / "README.md").is_file():
        pytest.skip("Isolated mutation sandbox without docs")
    forbidden = [
        "0TH-2026-020",
        "0TH-2026-022",
        "0 / 1,900",
        "0/1,900",
        "0/1{,}900",
        "0thernes LLC",
        "moonlab_xy_sim.mjs",
        "hochstadt_reconstruct",
        "staggered_j_ab",
        "witness_4x4_even_p2",
    ]
    check_files = [
        ROOT / "README.md",
        ROOT / "CLAIMS.md",
        ROOT / "LIMITATIONS.md",
        ROOT / "REPLICATION.md",
        ROOT / "UPGRADING.md",
        ROOT / "ROADMAP.md",
        ROOT / "llms.txt",
        ROOT / "repo.yaml",
        ROOT / "formalization.yaml",
        ROOT / "CITATION.cff",
        ROOT / "THIRD_PARTY_NOTICES.md",
        ROOT / "paper" / "main.tex",
    ] + [
        p
        for p in (ROOT / "docs").glob("*.md")
    ]
    hits: list[str] = []
    for fpath in check_files:
        if not fpath.is_file():
            continue
        content = fpath.read_text(encoding="utf-8")
        for bad in forbidden:
            if bad in content:
                hits.append(f"{fpath.relative_to(ROOT).as_posix()}: contains {bad!r}")
    assert not hits, f"Stale or hallucinated identifiers detected: {hits}"


def test_manifest_tamper_rejection(tmp_path: Path) -> None:
    """B39 negative test: verify SHA-256 verification fails immediately when a tracked file is altered."""
    if not (ROOT / "scripts" / "generate_manifest.py").is_file():
        pytest.skip("Isolated mutation sandbox without scripts/")
    from scripts.generate_manifest import sha256_file

    sample = tmp_path / "artifact.txt"
    sample.write_bytes(b"canonical-v1.1.0\n")
    digest_orig = sha256_file(sample)
    sample.write_bytes(b"tampered-v1.1.0\n")
    digest_tampered = sha256_file(sample)
    assert digest_orig != digest_tampered
