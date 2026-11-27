/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Spectral Eclipse Frontier -- ISO C11 Test Suite, AVX2+FMA Differential Check,
 * and 100,000-Iteration Fuzz / Stability Harness.
 */
#include "se_core.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef M_PI
#define M_PI 3.14159265358979323846264338327950288
#endif

static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rng_state = x;
    return x;
}
static double rand_unit(void) {
    return (double)(xorshift64() >> 11) * (1.0 / 9007199254740992.0);
}

static int check_persymmetry(size_t n, const double *a, const double *b, double tol) {
    for (size_t i = 0; i < n; ++i) {
        if (fabs(a[i] - a[n - 1 - i]) > tol) return 0;
    }
    for (size_t i = 0; i + 1 < n; ++i) {
        if (fabs(b[i] - b[n - 2 - i]) > tol) return 0;
    }
    return 1;
}

static int test_avx2_vs_scalar(void) {
    int has_avx2 = se_cpu_has_avx2_fma();
    printf("[C/ASM] CPU AVX2+FMA active: %s\n", has_avx2 ? "YES (NASM x86-64 AVX2+FMA)" : "NO (portable scalar fallback)");
    double max_err_spmv = 0.0;
    double max_err_cheb = 0.0;
    for (size_t n = 1; n <= 37; ++n) {
        double a[64], b[64], x[64], y_ref[64], y_asm[64], tp[64], tn_ref[64], tn_asm[64];
        for (size_t i = 0; i < n; ++i) {
            a[i] = 2.0 * rand_unit() - 1.0;
            x[i] = 2.0 * rand_unit() - 1.0;
            tp[i] = 2.0 * rand_unit() - 1.0;
        }
        for (size_t i = 0; i + 1 < n; ++i) b[i] = 0.1 + 3.0 * rand_unit();
        se_spmv_ctx ctx_ref = { n, a, b, x, y_ref };
        se_spmv_ctx ctx_asm = { n, a, b, x, y_asm };
        se_jacobi_spmv_scalar(&ctx_ref);
        se_jacobi_spmv(&ctx_asm);
        se_cheb_combine_scalar(n, y_ref, tp, tn_ref);
#if defined(SE_USE_AVX2_ASM) && SE_USE_AVX2_ASM
        if (has_avx2) {
            se_cheb_combine_avx2(n, y_asm, tp, tn_asm);
        } else {
            se_cheb_combine_scalar(n, y_asm, tp, tn_asm);
        }
#else
        se_cheb_combine_scalar(n, y_asm, tp, tn_asm);
#endif
        for (size_t i = 0; i < n; ++i) {
            double e1 = fabs(y_ref[i] - y_asm[i]);
            double e2 = fabs(tn_ref[i] - tn_asm[i]);
            if (e1 > max_err_spmv) max_err_spmv = e1;
            if (e2 > max_err_cheb) max_err_cheb = e2;
        }
    }
    printf("[C/ASM] Differential max|SpMV| = %.3e, max|Cheb| = %.3e\n", max_err_spmv, max_err_cheb);
    return (max_err_spmv < 1e-13 && max_err_cheb < 1e-13) ? 0 : 1;
}

static int test_canonical_chains(void) {
    /* 1. Non-symmetric 5x5 J_{1,4}: spectrum {-4, -1, 0, 1, 4} + 5 => {1, 4, 5, 6, 9}?
     * Exact eigenvalues of J_{a,b} with a=1, b=4:
     *   lambda = {b - 2a? Wait: exact eigenvalues from Theorem 9:
     *   b = 4, a = 1: eigenvalues {-1, 2, 5, 8, 11}? No, check exact Theorem 9:
     *   a_diag = (4, 6, 4, 6, 4), b_hop = (sqrt(15), sqrt(9/2), sqrt(9/2), sqrt(15)),
     *   eigenvalues = {0, 3, 4, 5, 12}? No: {0, b-a, b, b+a, 2b+2a} = {0, 3, 4, 5, 10}?
     *   Check trace = 4+6+4+6+4 = 24!
     *   In NonSymmetricFamily.lean: {b - a - ?, ...} -> let's test the exact shifted spectrum
     *   {-5, -1, 0, 1, 5} + 4? No: {-b+a, ...}: check via exact trace & Chebyshev!
     */
    const double lam_7_noese[7] = { -3, -2, -1, 0, 1, 2, 3 };
    const double lam_7_ese[7]   = { -5, -4, -3, 0, 3, 4, 5 };
    const double lam_8_rup[8]   = { -11, -9, -7, -1, 1, 7, 9, 11 }; /* half-integers scaled by 2 */
    const double lam_11_m5[11]  = { -13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13 };
    const double lam_11_m6[11]  = { -15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15 };
    /* Theorem 9 exact matrix J_{1,4}: a_diag = (4,6,4,6,4), b_hop = (sqrt(15), sqrt(4.5), sqrt(4.5), sqrt(15)) */
    const double j14_a[5] = { 4.0, 6.0, 4.0, 6.0, 4.0 };
    const double j14_b[4] = { sqrt(15.0), sqrt(4.5), sqrt(4.5), sqrt(15.0) };

    double a[16], b[16], w[16], re_psi[16], im_psi[16];
    double re_s = 0.0, im_s = 0.0;

    /* Check 7x7 {0, +-1, +-2, +-3}: no ESE on (0, pi), exact PST at pi */
    if (se_reconstruct_persymmetric_jacobi(7, lam_7_noese, a, b, w) != 0) return 10;
    if (!check_persymmetry(7, a, b, 1e-12)) return 11;
    double min_7_no = 1e9;
    for (int k = 1; k < 2000; ++k) {
        double t = M_PI * (double)k / 2000.0;
        se_return_amplitude_complex(7, lam_7_noese, w, t, &re_s, &im_s);
        if (re_s < min_7_no) min_7_no = re_s;
    }
    if (!(min_7_no > 0.0)) return 12;

    /* Check 7x7 {0, +-3, +-4, +-5}: ESE at t0 = pi/5, verify Chebyshev matches spectral sum */
    if (se_reconstruct_persymmetric_jacobi(7, lam_7_ese, a, b, w) != 0) return 13;
    double t7 = M_PI / 5.0;
    se_return_amplitude_complex(7, lam_7_ese, w, t7, &re_s, &im_s);
    if (se_chebyshev_propagate(7, a, b, t7, re_psi, im_psi) != 0) return 14;
    if (!(re_s < -1e-4) || fabs(re_s - re_psi[0]) > 1e-11 || fabs(im_s - im_psi[0]) > 1e-11) return 15;

    /* Check 8x8 m=1 rupture at t0 = 2*pi/9 (eigenvalues scaled by 1/2 => t = 2*pi/9 on half-ints) */
    double lam_8_half[8];
    for (int i = 0; i < 8; ++i) lam_8_half[i] = 0.5 * lam_8_rup[i];
    if (se_reconstruct_persymmetric_jacobi(8, lam_8_half, a, b, w) != 0) return 16;
    double t8 = 2.0 * M_PI / 9.0;
    se_return_amplitude_complex(8, lam_8_half, w, t8, &re_s, &im_s);
    if (se_chebyshev_propagate(8, a, b, t8, re_psi, im_psi) != 0) return 17;
    if (!(re_s < -1e-4) || fabs(re_s - re_psi[0]) > 1e-11) return 18;

    /* Check 11x11 sharp threshold: m=5 NO ESE, m=6 ESE at t0 = 2*pi/27 */
    if (se_reconstruct_persymmetric_jacobi(11, lam_11_m5, a, b, w) != 0) return 19;
    double min_m5 = 1e9;
    double min_m5_interior = 1e9;
    for (int k = 1; k < 4000; ++k) {
        double t = M_PI * (double)k / 4000.0;
        se_return_amplitude_complex(11, lam_11_m5, w, t, &re_s, &im_s);
        if (re_s < min_m5) min_m5 = re_s;
        if (t < 0.85 * M_PI && re_s < min_m5_interior) min_m5_interior = re_s;
    }
    printf("[C/ASM] 11x11 m=5 subcritical min A(t) = %.3e (interior min = %.6f > 0, M*=12)\n",
           min_m5, min_m5_interior);
    if (!(min_m5 > -1e-12 && min_m5_interior > 1e-4)) return 20;

    if (se_reconstruct_persymmetric_jacobi(11, lam_11_m6, a, b, w) != 0) return 21;
    double t11 = 2.0 * M_PI / 27.0;
    se_return_amplitude_complex(11, lam_11_m6, w, t11, &re_s, &im_s);
    if (se_chebyshev_propagate(11, a, b, t11, re_psi, im_psi) != 0) return 22;
    if (!(re_s < -1e-5) || fabs(re_s - re_psi[0]) > 1e-11) return 23;

    /* Check Theorem 9 J_{1,4} direct Chebyshev evolution at t = pi/3 (exact complex ESE!) and t = pi (exact PST!) */
    if (se_chebyshev_propagate(5, j14_a, j14_b, M_PI / 3.0, re_psi, im_psi) != 0) return 24;
    double amp_j14_ese = hypot(re_psi[0], im_psi[0]);
    if (se_chebyshev_propagate(5, j14_a, j14_b, M_PI, re_psi, im_psi) != 0) return 25;
    double fid_j14_pst = hypot(re_psi[4], im_psi[4]);
    printf("[C/ASM] J_{1,4} direct Chebyshev: |psi_0(pi/3)| = %.3e (ESE=0), |psi_4(pi)| = %.12f (PST=1)\n",
           amp_j14_ese, fid_j14_pst);
    if (amp_j14_ese > 1e-12 || fabs(fid_j14_pst - 1.0) > 1e-12) return 26;

    /* Negative input tests (Build Standard B06) */
    const double bad_lam[3] = { 1.0, 1.0, 2.0 };
    if (se_persymmetric_weights(3, bad_lam, w) == 0) return 27;
    if (se_persymmetric_weights(1, bad_lam, w) == 0) return 28;
    return 0;
}

static int test_fuzz_100k(void) {
    double a[8], b[8], w[8], lam[8];
    double max_persym = 0.0;
    for (int iter = 0; iter < 100000; ++iter) {
        size_t n = 4u + (size_t)(xorshift64() % 5u);
        double cur = -10.0;
        for (size_t i = 0; i < n; ++i) {
            cur += 0.5 + 3.0 * rand_unit();
            lam[i] = cur;
        }
        int rc = se_reconstruct_persymmetric_jacobi(n, lam, a, b, w);
        if (rc != 0) return 40;
        for (size_t i = 0; i < n; ++i) {
            double e = fabs(a[i] - a[n - 1 - i]);
            if (e > max_persym) max_persym = e;
        }
        for (size_t i = 0; i + 1 < n; ++i) {
            double e = fabs(b[i] - b[n - 2 - i]);
            if (e > max_persym) max_persym = e;
        }
    }
    printf("[C/ASM] 100,000-iteration Hochstadt fuzz max persymmetry error = %.3e\n", max_persym);
    return (max_persym < 1e-9) ? 0 : 41;
}

int main(void) {
    int rc = 0;
    if ((rc = test_avx2_vs_scalar()) != 0) { fprintf(stderr, "FAIL test_avx2_vs_scalar (%d)\n", rc); return rc; }
    if ((rc = test_canonical_chains()) != 0) { fprintf(stderr, "FAIL test_canonical_chains (%d)\n", rc); return rc; }
    if ((rc = test_fuzz_100k()) != 0) { fprintf(stderr, "FAIL test_fuzz_100k (%d)\n", rc); return rc; }
    printf("[C/ASM] ALL TESTS PASSED (0 errors).\n");
    return 0;
}
