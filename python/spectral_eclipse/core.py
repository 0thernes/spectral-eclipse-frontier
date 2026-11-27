# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Core Python API for Spectral Eclipse Frontier."""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass

import numpy as np
from numpy.typing import NDArray


@dataclass(frozen=True)
class JacobiChain:
    """Persymmetric tridiagonal Jacobi Hamiltonian reconstructed from spectrum."""

    eigenvalues: tuple[float, ...]
    diag_a: tuple[float, ...]
    off_b: tuple[float, ...]
    weights: tuple[float, ...]

    @property
    def dimension(self) -> int:
        return len(self.eigenvalues)

    @property
    def b0_sq(self) -> float:
        return self.off_b[0] ** 2

    @property
    def qsl_bound(self) -> float:
        return math.pi / (2.0 * self.off_b[0])


def persymmetric_weights(eigenvalues: Sequence[float]) -> NDArray[np.float64]:
    """Compute exact normalized persymmetric spectral weights w_k = |q_k(0)|^2."""
    lam = np.asarray(eigenvalues, dtype=np.float64)
    if lam.ndim != 1 or lam.size < 2:
        raise ValueError("eigenvalues must be a 1-D sequence of length >= 2")
    if not bool(np.all(np.diff(lam) > 0.0)):
        raise ValueError("eigenvalues must be strictly increasing")
    n = lam.size
    log_inv = np.zeros(n, dtype=np.float64)
    for k in range(n):
        diffs = np.abs(lam[k] - np.delete(lam, k))
        log_inv[k] = -float(np.sum(np.log(diffs)))
    log_inv -= float(np.max(log_inv))
    w = np.exp(log_inv)
    w /= float(np.sum(w))
    return w


def reconstruct_persymmetric_jacobi(eigenvalues: Sequence[float]) -> JacobiChain:
    """Reconstruct the unique persymmetric Jacobi matrix J via Lanczos + two-pass MGS."""
    lam = np.asarray(eigenvalues, dtype=np.float64)
    w = persymmetric_weights(eigenvalues)
    n = lam.size
    q_mat = np.zeros((n, n), dtype=np.float64)
    q_mat[0, :] = np.sqrt(w)
    a_out = np.zeros(n, dtype=np.float64)
    b_out = np.zeros(n - 1, dtype=np.float64)
    for j in range(n):
        alpha = float(np.sum(lam * q_mat[j, :] ** 2))
        a_out[j] = alpha
        if j + 1 == n:
            break
        beta_prev = 0.0 if j == 0 else b_out[j - 1]
        v = (lam - alpha) * q_mat[j, :] - (0.0 if j == 0 else beta_prev * q_mat[j - 1, :])
        for _ in range(2):
            for m in range(j + 1):
                v -= float(np.dot(v, q_mat[m, :])) * q_mat[m, :]
        beta = float(np.linalg.norm(v))
        if beta <= 0.0 or not math.isfinite(beta):
            raise RuntimeError("Lanczos breakdown during persymmetric reconstruction")
        b_out[j] = beta
        q_mat[j + 1, :] = v / beta
    return JacobiChain(
        eigenvalues=tuple(float(x) for x in lam),
        diag_a=tuple(float(x) for x in a_out),
        off_b=tuple(float(x) for x in b_out),
        weights=tuple(float(x) for x in w),
    )


def return_amplitude(chain: JacobiChain, t: float) -> complex:
    """Evaluate exact complex return amplitude <e_0 | e^{-i J t} | e_0>."""
    lam = np.asarray(chain.eigenvalues, dtype=np.float64)
    w = np.asarray(chain.weights, dtype=np.float64)
    phases = -lam * float(t)
    return complex(float(np.sum(w * np.cos(phases))), float(np.sum(w * np.sin(phases))))


def target_amplitude(chain: JacobiChain, t: float) -> complex:
    """Evaluate exact complex mirror-end amplitude <e_{N-1} | e^{-i J t} | e_0>."""
    n = chain.dimension
    lam = np.asarray(chain.eigenvalues, dtype=np.float64)
    w = np.asarray(chain.weights, dtype=np.float64)
    signs = np.array([1.0 if ((n - 1 - k) % 2 == 0) else -1.0 for k in range(n)], dtype=np.float64)
    phases = -lam * float(t)
    return complex(float(np.sum(signs * w * np.cos(phases))), float(np.sum(signs * w * np.sin(phases))))


def detect_real_ese(chain: JacobiChain, pst_time: float = math.pi, grid: int = 4000) -> tuple[bool, float | None]:
    """Detect real-amplitude Early State Exclusion on (0, pst_time) with cancellation guard."""
    ts = np.linspace(0.0, pst_time, grid + 1)[1:-1]
    prev = 1.0
    prev_t = 0.0
    min_re = 1.0
    for t in ts:
        re = return_amplitude(chain, float(t)).real
        min_re = min(min_re, re)
        if prev > 1e-11 and re < -1e-11:
            lo, hi = prev_t, float(t)
            for _ in range(60):
                mid = 0.5 * (lo + hi)
                if return_amplitude(chain, mid).real > 0.0:
                    lo = mid
                else:
                    hi = mid
            return True, 0.5 * (lo + hi)
        prev, prev_t = re, float(t)
    return (min_re < -1e-10), None
