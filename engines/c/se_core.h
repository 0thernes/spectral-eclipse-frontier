/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Spectral Eclipse Frontier -- ISO C11 Core Engine Header
 * Exact Hochstadt persymmetric inverse-eigenvalue reconstruction,
 * AVX2+FMA tridiagonal Jacobi SpMV / Chebyshev propagation, and
 * Early State Exclusion (ESE) diagnostics.
 */
#ifndef SE_CORE_H
#define SE_CORE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct se_spmv_ctx {
    size_t n;
    const double *a;
    const double *b;
    const double *x;
    double *y;
} se_spmv_ctx;

/* Assembly AVX2+FMA kernels (linked on x86-64 builds with SE_USE_AVX2_ASM=1). */
#if defined(SE_USE_AVX2_ASM) && SE_USE_AVX2_ASM
void se_jacobi_spmv_avx2(const se_spmv_ctx *ctx);
void se_cheb_combine_avx2(size_t n, const double *jx,
                          const double *t_prev, double *t_next);
#endif

/* Portable scalar reference implementations. */
void se_jacobi_spmv_scalar(const se_spmv_ctx *ctx);
void se_cheb_combine_scalar(size_t n, const double *jx,
                            const double *t_prev, double *t_next);

/* Runtime-dispatched SpMV (uses AVX2+FMA ASM when compiled and supported). */
int se_cpu_has_avx2_fma(void);
void se_jacobi_spmv(const se_spmv_ctx *ctx);

/*
 * Persymmetric Jacobi matrix reconstruction (Hochstadt / de Boor-Golub Lanczos).
 * Given n strictly increasing eigenvalues lambda[0] < ... < lambda[n-1],
 * computes the unique persymmetric Jacobi matrix J (a[0..n-1], b[0..n-2] > 0)
 * and spectral weights w[0..n-1] = |q_k(0)|^2 satisfying:
 *   w_k = c / prod_{j != k} |lambda_k - lambda_j|,  sum_k w_k = 1.
 * Returns 0 on success, non-zero on invalid input (non-strict spectrum or n < 2).
 */
int se_persymmetric_weights(size_t n, const double *lambda, double *w_out);
int se_reconstruct_persymmetric_jacobi(size_t n, const double *lambda,
                                       double *a_out, double *b_out,
                                       double *w_out);

/*
 * Return amplitude A(t) = Re(<e_0 | e^{-i J t} | e_0>) and full complex
 * return/target amplitudes for persymmetric PST chains with integer spectrum.
 */
void se_return_amplitude_complex(size_t n, const double *lambda, const double *w,
                                 double t, double *re_out, double *im_out);
void se_target_amplitude_complex(size_t n, const double *lambda, const double *w,
                                 double t, double *re_out, double *im_out);

/*
 * Chebyshev polynomial propagation of e^{-i J t} e_0 using AVX2+FMA SpMV
 * (verifying direct matrix dynamics against spectral sum independently).
 */
int se_chebyshev_propagate(size_t n, const double *a, const double *b,
                           double t, double *psi_re, double *psi_im);

#ifdef __cplusplus
}
#endif

#endif /* SE_CORE_H */
