# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Spectral Eclipse Frontier Python reference package."""

from spectral_eclipse.core import (
    FLOAT64_CANCELLATION_MARGIN,
    FLOAT64_MIN_RE_THRESHOLD,
    JacobiChain,
    detect_real_ese,
    persymmetric_weights,
    reconstruct_persymmetric_jacobi,
    return_amplitude,
    target_amplitude,
)

__all__ = [
    "FLOAT64_CANCELLATION_MARGIN",
    "FLOAT64_MIN_RE_THRESHOLD",
    "JacobiChain",
    "detect_real_ese",
    "persymmetric_weights",
    "reconstruct_persymmetric_jacobi",
    "return_amplitude",
    "target_amplitude",
]
__version__ = "1.1.0"
