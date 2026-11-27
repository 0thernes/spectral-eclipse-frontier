/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Spectral Eclipse Frontier -- ISO C11 Core Engine Implementation
 * Zero undefined behavior, strict C11 (-Wall -Wextra -Werror),
 * dual runtime dispatch to NASM x86-64 AVX2+FMA assembly kernels.
 */
#include "se_core.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

#if defined(__x86_64__) || defined(_M_X64)
#if defined(_MSC_VER)
#include <intrin.h>
#elif defined(__GNUC__) || defined(__clang__)
#include <cpuid.h>
#endif
#endif

int se_cpu_has_avx2_fma(void) {
#if defined(SE_USE_AVX2_ASM) && SE_USE_AVX2_ASM && (defined(__x86_64__) || defined(_M_X64))
    unsigned int eax = 0, ebx = 0, ecx = 0, edx = 0;
#if defined(_MSC_VER)
    int regs[4] = {0, 0, 0, 0};
    __cpuid(regs, 1);
    ecx = (unsigned int)regs[2];
    int has_fma = (ecx & (1u << 12)) != 0;
    int has_osxsave = (ecx & (1u << 27)) != 0;
    if (!has_fma || !has_osxsave) return 0;
    unsigned long long xcr0 = _xgetbv(0);
    if ((xcr0 & 0x6u) != 0x6u) return 0;
    __cpuidex(regs, 7, 0);
    ebx = (unsigned int)regs[1];
    return (ebx & (1u << 5)) != 0;
#else
    if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx)) return 0;
    int has_fma = (ecx & (1u << 12)) != 0;
    int has_osxsave = (ecx & (1u << 27)) != 0;
    if (!has_fma || !has_osxsave) return 0;
    unsigned int xcr0_lo = 0, xcr0_hi = 0;
    __asm__ __volatile__("xgetbv" : "=a"(xcr0_lo), "=d"(xcr0_hi) : "c"(0));
    if ((xcr0_lo & 0x6u) != 0x6u) return 0;
    if (!__get_cpuid_count(7, 0, &eax, &ebx, &ecx, &edx)) return 0;
    return (ebx & (1u << 5)) != 0;
#endif
#else
    return 0;
#endif
}

void se_jacobi_spmv_scalar(const se_spmv_ctx *ctx) {
    if (!ctx || ctx->n == 0) return;
    const size_t n = ctx->n;
    const double *a = ctx->a;
    const double *b = ctx->b;
    const double *x = ctx->x;
    double *y = ctx->y;
    if (n == 1) {
        y[0] = a[0] * x[0];
        return;
    }
    y[0] = a[0] * x[0] + b[0] * x[1];
    for (size_t i = 1; i + 1 < n; ++i) {
        y[i] = b[i - 1] * x[i - 1] + a[i] * x[i] + b[i] * x[i + 1];
    }
    y[n - 1] = b[n - 2] * x[n - 2] + a[n - 1] * x[n - 1];
}

void se_cheb_combine_scalar(size_t n, const double *jx,
                            const double *t_prev, double *t_next) {
    for (size_t i = 0; i < n; ++i) {
        t_next[i] = 2.0 * jx[i] - t_prev[i];
    }
}

void se_jacobi_spmv(const se_spmv_ctx *ctx) {
#if defined(SE_USE_AVX2_ASM) && SE_USE_AVX2_ASM
    if (se_cpu_has_avx2_fma()) {
        se_jacobi_spmv_avx2(ctx);
        return;
    }
#endif
    se_jacobi_spmv_scalar(ctx);
}

int se_persymmetric_weights(size_t n, const double *lambda, double *w_out) {
    if (n < 2 || !lambda || !w_out) return -1;
    for (size_t i = 0; i + 1 < n; ++i) {
        if (!(lambda[i] < lambda[i + 1])) return -2;
    }
    /* Compute log-scaled inverse products to prevent overflow for large N. */
    double *log_inv = (double *)malloc(n * sizeof(double));
    if (!log_inv) return -3;
    double max_log = -INFINITY;
    for (size_t k = 0; k < n; ++k) {
        double s = 0.0;
        for (size_t j = 0; j < n; ++j) {
            if (j == k) continue;
            s -= log(fabs(lambda[k] - lambda[j]));
        }
        log_inv[k] = s;
        if (s > max_log) max_log = s;
    }
    double sum = 0.0;
    for (size_t k = 0; k < n; ++k) {
        w_out[k] = exp(log_inv[k] - max_log);
        sum += w_out[k];
    }
    free(log_inv);
    if (!(sum > 0.0) || !isfinite(sum)) return -4;
    for (size_t k = 0; k < n; ++k) {
        w_out[k] /= sum;
    }
    return 0;
}

int se_reconstruct_persymmetric_jacobi(size_t n, const double *lambda,
                                       double *a_out, double *b_out,
                                       double *w_out) {
    if (n < 2 || !lambda || !a_out || !b_out) return -1;
    double *w = (double *)malloc(n * sizeof(double));
    double *q_prev = (double *)calloc(n, sizeof(double));
    double *q_curr = (double *)malloc(n * sizeof(double));
    double *q_next = (double *)malloc(n * sizeof(double));
    double *Q = (double *)malloc(n * n * sizeof(double));
    if (!w || !q_prev || !q_curr || !q_next || !Q) {
        free(w); free(q_prev); free(q_curr); free(q_next); free(Q);
        return -3;
    }
    int rc = se_persymmetric_weights(n, lambda, w);
    if (rc != 0) {
        free(w); free(q_prev); free(q_curr); free(q_next); free(Q);
        return rc;
    }
    if (w_out) memcpy(w_out, w, n * sizeof(double));

    /*
     * Stieltjes / Lanczos orthogonalization with full Modified Gram-Schmidt
     * reorthogonalization against previous basis vectors for machine precision.
     */
    for (size_t k = 0; k < n; ++k) {
        q_curr[k] = sqrt(w[k]);
        Q[k] = q_curr[k];
    }
    for (size_t j = 0; j < n; ++j) {
        double alpha = 0.0;
        for (size_t k = 0; k < n; ++k) {
            alpha += lambda[k] * q_curr[k] * q_curr[k];
        }
        a_out[j] = alpha;
        if (j + 1 == n) break;
        double beta_prev = (j == 0) ? 0.0 : b_out[j - 1];
        for (size_t k = 0; k < n; ++k) {
            q_next[k] = (lambda[k] - alpha) * q_curr[k] - beta_prev * q_prev[k];
        }
        /* Two passes of MGS reorthogonalization against Q[0..j]. */
        for (int pass = 0; pass < 2; ++pass) {
            for (size_t m = 0; m <= j; ++m) {
                double dot = 0.0;
                const double *qm = &Q[m * n];
                for (size_t k = 0; k < n; ++k) dot += q_next[k] * qm[k];
                for (size_t k = 0; k < n; ++k) q_next[k] -= dot * qm[k];
            }
        }
        double norm2 = 0.0;
        for (size_t k = 0; k < n; ++k) norm2 += q_next[k] * q_next[k];
        double beta = sqrt(norm2);
        if (!(beta > 0.0) || !isfinite(beta)) {
            free(w); free(q_prev); free(q_curr); free(q_next); free(Q);
            return -5;
        }
        b_out[j] = beta;
        for (size_t k = 0; k < n; ++k) {
            q_prev[k] = q_curr[k];
            q_curr[k] = q_next[k] / beta;
            Q[(j + 1) * n + k] = q_curr[k];
        }
    }
    free(w); free(q_prev); free(q_curr); free(q_next); free(Q);
    return 0;
}

void se_return_amplitude_complex(size_t n, const double *lambda, const double *w,
                                 double t, double *re_out, double *im_out) {
    double re = 0.0, im = 0.0;
    for (size_t k = 0; k < n; ++k) {
        double phase = lambda[k] * t;
        re += w[k] * cos(phase);
        im -= w[k] * sin(phase);
    }
    if (re_out) *re_out = re;
    if (im_out) *im_out = im;
}

void se_target_amplitude_complex(size_t n, const double *lambda, const double *w,
                                 double t, double *re_out, double *im_out) {
    double re = 0.0, im = 0.0;
    for (size_t k = 0; k < n; ++k) {
        double sgn = (((n - 1 - k) & 1u) == 0u) ? 1.0 : -1.0;
        double phase = lambda[k] * t;
        re += sgn * w[k] * cos(phase);
        im -= sgn * w[k] * sin(phase);
    }
    if (re_out) *re_out = re;
    if (im_out) *im_out = im;
}

/* Bessel function J_m(z) via Miller's backward recurrence (stable for all m >= 0). */
static void bessel_j_array(double z, int max_m, double *jm_out) {
    if (z == 0.0) {
        jm_out[0] = 1.0;
        for (int m = 1; m <= max_m; ++m) jm_out[m] = 0.0;
        return;
    }
    int start = max_m + (int)(40.0 + 1.5 * fabs(z));
    if (start < max_m + 40) start = max_m + 40;
    double *tmp = (double *)calloc((size_t)(start + 2), sizeof(double));
    if (!tmp) return;
    tmp[start] = 1e-200;
    tmp[start + 1] = 0.0;
    for (int k = start; k >= 1; --k) {
        tmp[k - 1] = (2.0 * (double)k / z) * tmp[k] - tmp[k + 1];
        if (fabs(tmp[k - 1]) > 1e150) {
            for (int j = k - 1; j <= start; ++j) tmp[j] *= 1e-150;
        }
    }
    /* Normalization: J_0(z) + 2 * sum_{k>=1} J_{2k}(z) = 1. */
    double norm = tmp[0];
    for (int k = 2; k <= start; k += 2) norm += 2.0 * tmp[k];
    for (int m = 0; m <= max_m; ++m) jm_out[m] = tmp[m] / norm;
    free(tmp);
}

int se_chebyshev_propagate(size_t n, const double *a, const double *b,
                           double t, double *psi_re, double *psi_im) {
    if (n < 2 || !a || !b || !psi_re || !psi_im) return -1;
    /* Gershgorin spectral envelope [e_min, e_max]. */
    double e_min = INFINITY, e_max = -INFINITY;
    for (size_t i = 0; i < n; ++i) {
        double r = 0.0;
        if (i > 0) r += fabs(b[i - 1]);
        if (i + 1 < n) r += fabs(b[i]);
        if (a[i] - r < e_min) e_min = a[i] - r;
        if (a[i] + r > e_max) e_max = a[i] + r;
    }
    double center = 0.5 * (e_max + e_min);
    double half = 0.5 * (e_max - e_min) * 1.02 + 1e-6;
    double *a_s = (double *)malloc(n * sizeof(double));
    double *b_s = (double *)malloc((n - 1) * sizeof(double));
    double *t_prev = (double *)calloc(n, sizeof(double));
    double *t_curr = (double *)calloc(n, sizeof(double));
    double *t_next = (double *)calloc(n, sizeof(double));
    double *jx = (double *)calloc(n, sizeof(double));
    if (!a_s || !b_s || !t_prev || !t_curr || !t_next || !jx) {
        free(a_s); free(b_s); free(t_prev); free(t_curr); free(t_next); free(jx);
        return -3;
    }
    for (size_t i = 0; i < n; ++i) a_s[i] = (a[i] - center) / half;
    for (size_t i = 0; i + 1 < n; ++i) b_s[i] = b[i] / half;

    double tau = half * fabs(t);
    int max_m = (int)(tau * 1.35 + 48.0);
    double *jm = (double *)calloc((size_t)(max_m + 1), sizeof(double));
    double *acc_re = (double *)calloc(n, sizeof(double));
    double *acc_im = (double *)calloc(n, sizeof(double));
    if (!jm || !acc_re || !acc_im) {
        free(a_s); free(b_s); free(t_prev); free(t_curr); free(t_next);
        free(jx); free(jm); free(acc_re); free(acc_im);
        return -3;
    }
    bessel_j_array(tau, max_m, jm);

    /* T_0(H_s) e_0 = e_0 */
    t_prev[0] = 1.0;
    acc_re[0] += jm[0];

    /* T_1(H_s) e_0 = H_s e_0 */
    se_spmv_ctx ctx1 = { n, a_s, b_s, t_prev, t_curr };
    se_jacobi_spmv(&ctx1);
    double sgn_t = (t >= 0.0) ? 1.0 : -1.0;

    for (int m = 1; m <= max_m; ++m) {
        const double *vec = (m == 1) ? t_curr : t_next;
        if (m >= 2) {
            se_spmv_ctx ctx = { n, a_s, b_s, t_curr, jx };
            se_jacobi_spmv(&ctx);
#if defined(SE_USE_AVX2_ASM) && SE_USE_AVX2_ASM
            if (se_cpu_has_avx2_fma()) {
                se_cheb_combine_avx2(n, jx, t_prev, t_next);
            } else {
                se_cheb_combine_scalar(n, jx, t_prev, t_next);
            }
#else
            se_cheb_combine_scalar(n, jx, t_prev, t_next);
#endif
        }
        /* (-i * sgn_t)^m * 2 * J_m(tau) */
        double c = 2.0 * jm[m];
        int mod4 = m & 3;
        if (mod4 == 0) {
            for (size_t i = 0; i < n; ++i) acc_re[i] += c * vec[i];
        } else if (mod4 == 1) {
            for (size_t i = 0; i < n; ++i) acc_im[i] -= sgn_t * c * vec[i];
        } else if (mod4 == 2) {
            for (size_t i = 0; i < n; ++i) acc_re[i] -= c * vec[i];
        } else {
            for (size_t i = 0; i < n; ++i) acc_im[i] += sgn_t * c * vec[i];
        }
        if (m >= 2) {
            double *tmp_ptr = t_prev;
            t_prev = t_curr;
            t_curr = t_next;
            t_next = tmp_ptr;
        }
    }

    /* Multiply by global phase e^{-i * center * t}. */
    double c_ph = cos(center * t);
    double s_ph = -sin(center * t);
    for (size_t i = 0; i < n; ++i) {
        psi_re[i] = acc_re[i] * c_ph - acc_im[i] * s_ph;
        psi_im[i] = acc_re[i] * s_ph + acc_im[i] * c_ph;
    }

    free(a_s); free(b_s); free(t_prev); free(t_curr); free(t_next);
    free(jx); free(jm); free(acc_re); free(acc_im);
    return 0;
}
