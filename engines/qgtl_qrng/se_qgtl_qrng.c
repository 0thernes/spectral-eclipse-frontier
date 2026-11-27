/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Spectral Eclipse Frontier -- Vendored QGTL + Quantum-RNG Engine
 *
 * Links BOTH real vendored C libraries:
 *   1. QGTL (third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c)
 *      -> Computes exact Fubini-Study distances d_FS(psi(0), psi(t)) on CP^{N-1},
 *         verifies Fubini-Study metric velocity g_{tt} = (d_FS(t, t+dt)/dt)^2 == b_0^2
 *         (Theorem 10 exact quantum geometric metric identity!) and verifies
 *         d_FS(psi(0), psi(tau_ESE)) == pi/2 at Early State Exclusion.
 *   2. Quantum-RNG (third_party/quantum_rng/src/quantum_rng/quantum_rng.c)
 *      -> Executes the PRE-REGISTERED 4-arm x 5-disorder x 30-seed paired diagonal-disorder
 *         robustness study locked in PREREGISTRATION.md BEFORE code execution!
 *         Emits complete machine-readable per-seed + summary JSON to results/qgtl_qrng_study.json.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "quantum_geometric/distributed/differential_geometry.h"
#include "quantum_rng.h"
#include "../c/se_core.h"

#ifndef M_PI
#define M_PI 3.14159265358979323846264338327950288
#endif

/* Direct real symmetric tridiagonal QL eigendecomposition (handles arbitrary disordered J_eps). */
static int tridiag_ql_c(size_t n, const double *diag_in, const double *off_in,
                        double *evals_out, double *evec0_out) {
    double *d = (double *)malloc(n * sizeof(double));
    double *e = (double *)calloc(n, sizeof(double));
    double *z = (double *)calloc(n * n, sizeof(double));
    if (!d || !e || !z) { free(d); free(e); free(z); return -1; }
    for (size_t i = 0; i < n; ++i) {
        d[i] = diag_in[i];
        z[i * n + i] = 1.0;
    }
    for (size_t i = 0; i + 1 < n; ++i) e[i] = off_in[i];

    for (size_t l = 0; l < n; ++l) {
        int iter = 0;
        size_t m = l;
        do {
            for (m = l; m + 1 < n; ++m) {
                double dd = fabs(d[m]) + fabs(d[m + 1]);
                if (fabs(e[m]) <= 2.220446049250313e-16 * dd) break;
            }
            if (m != l) {
                if (++iter > 120) { free(d); free(e); free(z); return -2; }
                double g = (d[l + 1] - d[l]) / (2.0 * e[l]);
                double r = hypot(g, 1.0);
                g = d[m] - d[l] + e[l] / (g + copysign(r, g));
                double s = 1.0, c = 1.0, p = 0.0;
                for (size_t i = m; i-- > l;) {
                    double f = s * e[i];
                    double b = c * e[i];
                    r = hypot(f, g);
                    e[i + 1] = r;
                    if (r == 0.0) {
                        d[i + 1] -= p;
                        e[m] = 0.0;
                        break;
                    }
                    s = f / r;
                    c = g / r;
                    g = d[i + 1] - p;
                    r = (d[i] - g) * s + 2.0 * c * b;
                    p = s * r;
                    d[i + 1] = g + p;
                    g = c * r - b;
                    for (size_t k = 0; k < n; ++k) {
                        double zk = z[k * n + (i + 1)];
                        z[k * n + (i + 1)] = s * z[k * n + i] + c * zk;
                        z[k * n + i] = c * z[k * n + i] - s * zk;
                    }
                }
                if (!(e[m] == 0.0 && m != l)) {
                    d[l] -= p;
                    e[l] = g;
                    e[m] = 0.0;
                }
            }
        } while (m != l);
    }

    for (size_t k = 0; k < n; ++k) {
        evals_out[k] = d[k];
        /* Row 0 of eigenvector matrix z[0 * n + k] gives <e_0 | v_k> */
        evec0_out[k] = z[0 * n + k];
    }
    free(d); free(e); free(z);
    return 0;
}

static double return_amp_abs(size_t n, const double *evals, const double *evec0, double t) {
    double re = 0.0, im = 0.0;
    for (size_t k = 0; k < n; ++k) {
        double w = evec0[k] * evec0[k];
        double ph = evals[k] * t;
        re += w * cos(ph);
        im -= w * sin(ph);
    }
    return hypot(re, im);
}

/* Pre-registered interior minimum m(J_eps) = min_{t in [0.05*T0, 0.95*T0]} |<e_0|e^{-i J_eps t}|e_0>|
 * via 500-point uniform interior grid + golden-section refinement (matches PREREGISTRATION.md!). */
static double compute_interior_min(size_t n, const double *evals, const double *evec0,
                                   double t0, double *tau_min_out) {
    const int grid = 500;
    const double t_lo = 0.05 * t0;
    const double t_hi = 0.95 * t0;
    double best_val = 1e9;
    int best_idx = 0;
    for (int i = 0; i <= grid; ++i) {
        double t = t_lo + (t_hi - t_lo) * (double)i / (double)grid;
        double v = return_amp_abs(n, evals, evec0, t);
        if (v < best_val) {
            best_val = v;
            best_idx = i;
        }
    }
    double a = t_lo + (t_hi - t_lo) * (double)(best_idx > 0 ? best_idx - 1 : 0) / (double)grid;
    double b = t_lo + (t_hi - t_lo) * (double)(best_idx < grid ? best_idx + 1 : grid) / (double)grid;
    const double inv_phi = 0.6180339887498949;
    double c = b - inv_phi * (b - a);
    double d = a + inv_phi * (b - a);
    double fc = return_amp_abs(n, evals, evec0, c);
    double fd = return_amp_abs(n, evals, evec0, d);
    for (int it = 0; it < 50; ++it) {
        if (fc < fd) {
            b = d; d = c; fd = fc;
            c = b - inv_phi * (b - a);
            fc = return_amp_abs(n, evals, evec0, c);
        } else {
            a = c; c = d; fc = fd;
            d = a + inv_phi * (b - a);
            fd = return_amp_abs(n, evals, evec0, d);
        }
    }
    double t_opt = 0.5 * (a + b);
    double v_opt = return_amp_abs(n, evals, evec0, t_opt);
    if (tau_min_out) *tau_min_out = t_opt;
    return v_opt;
}

typedef struct {
    const char *name;
    size_t n;
    double a[16];
    double b[16];
    double b_mean;
    double b0;
    double tau_ideal;
} ChainSpec;

static void init_chain_from_spec(ChainSpec *cs, const char *name, size_t n, const double *lam) {
    cs->name = name;
    cs->n = n;
    double w[16];
    if (se_reconstruct_persymmetric_jacobi(n, lam, cs->a, cs->b, w) != 0) {
        fprintf(stderr, "Failed to reconstruct %s\n", name);
        exit(2);
    }
    double sum_b = 0.0;
    for (size_t i = 0; i + 1 < n; ++i) sum_b += cs->b[i];
    cs->b_mean = sum_b / (double)(n - 1);
    cs->b0 = cs->b[0];
    double evals[16], evec0[16];
    tridiag_ql_c(n, cs->a, cs->b, evals, evec0);
    /* Locate FIRST real-amplitude zero crossing tau_1 in (0, pi) for exact QSL efficiency eta! */
    cs->tau_ideal = M_PI;
    double prev_re = 1.0;
    for (int s = 1; s < 4000; ++s) {
        double t = M_PI * (double)s / 4000.0;
        double re = 0.0;
        for (size_t k = 0; k < n; ++k) re += (evec0[k] * evec0[k]) * cos(evals[k] * t);
        if (prev_re > 1e-11 && re < -1e-11) {
            double lo = M_PI * (double)(s - 1) / 4000.0;
            double hi = t;
            for (int it = 0; it < 60; ++it) {
                double mid = 0.5 * (lo + hi);
                double rmid = 0.0;
                for (size_t k = 0; k < n; ++k) rmid += (evec0[k] * evec0[k]) * cos(evals[k] * mid);
                if (rmid > 0.0) lo = mid; else hi = mid;
            }
            cs->tau_ideal = 0.5 * (lo + hi);
            break;
        }
        prev_re = re;
    }
}

static void init_chain_j14(ChainSpec *cs) {
    cs->name = "5x5_J14_staggered";
    cs->n = 5;
    cs->a[0] = 4.0; cs->a[1] = 6.0; cs->a[2] = 4.0; cs->a[3] = 6.0; cs->a[4] = 4.0;
    cs->b[0] = sqrt(15.0); cs->b[1] = sqrt(4.5); cs->b[2] = sqrt(4.5); cs->b[3] = sqrt(15.0);
    cs->b_mean = 0.25 * (cs->b[0] + cs->b[1] + cs->b[2] + cs->b[3]);
    cs->b0 = cs->b[0];
    cs->tau_ideal = M_PI / 3.0;
}

/* Verify Theorem 10 Fubini-Study metric velocity g_{tt} == b_0^2 and d_FS(0, tau_ESE) == pi/2 using REAL QGTL! */
static int verify_qgtl_geometry(const ChainSpec *cs, double *gtt_out, double *dfs_ese_out, double *eta_out) {
    diffgeo_config_t cfg = diffgeo_default_config();
    cfg.manifold_type = MANIFOLD_PROJECTIVE_HILBERT;
    cfg.metric_type = METRIC_FUBINI_STUDY;
    diffgeo_engine_t *eng = diffgeo_engine_create_with_config(&cfg);
    if (!eng) return -1;

    double psi0_re[16], psi0_im[16], psidt_re[16], psidt_im[16], psie_re[16], psie_im[16];
    const double dt = 1e-6;
    se_chebyshev_propagate(cs->n, cs->a, cs->b, 0.0, psi0_re, psi0_im);
    se_chebyshev_propagate(cs->n, cs->a, cs->b, dt, psidt_re, psidt_im);
    se_chebyshev_propagate(cs->n, cs->a, cs->b, cs->tau_ideal, psie_re, psie_im);

    ComplexDouble c0[16], cdt[16], ce[16];
    for (size_t i = 0; i < cs->n; ++i) {
        c0[i].real = psi0_re[i]; c0[i].imag = psi0_im[i];
        cdt[i].real = psidt_re[i]; cdt[i].imag = psidt_im[i];
        ce[i].real = psie_re[i]; ce[i].imag = psie_im[i];
    }
    diffgeo_point_t *p0 = diffgeo_point_create(eng, c0, cs->n);
    diffgeo_point_t *pdt = diffgeo_point_create(eng, cdt, cs->n);
    diffgeo_point_t *pe = diffgeo_point_create(eng, ce, cs->n);
    if (!p0 || !pdt || !pe) {
        diffgeo_engine_destroy(eng);
        return -2;
    }

    double d_dt = diffgeo_distance(eng, p0, pdt);
    double d_ese = diffgeo_distance(eng, p0, pe);
    double g_tt = (d_dt / dt) * (d_dt / dt);
    double eta = (M_PI / (2.0 * cs->b0)) / cs->tau_ideal;

    *gtt_out = g_tt;
    *dfs_ese_out = d_ese;
    *eta_out = eta;

    diffgeo_point_destroy(p0);
    diffgeo_point_destroy(pdt);
    diffgeo_point_destroy(pe);
    diffgeo_engine_destroy(eng);
    return 0;
}

int main(int argc, char **argv) {
    const char *json_path = (argc > 1) ? argv[1] : "../../results/qgtl_qrng_study.json";

    /* Define the 4 pre-registered pairs (H1, H2, H3, H4) from PREREGISTRATION.md */
    const double lam_h1_t[7]  = { -5, -4, -3, 0, 3, 4, 5 };
    const double lam_h1_c[7]  = { -5, -2, -1, 0, 1, 2, 5 };
    const double lam_h2_t[8]  = { -5.5, -4.5, -3.5, -0.5, 0.5, 3.5, 4.5, 5.5 };
    const double lam_h2_c[6]  = { -3.5, -2.5, -0.5, 0.5, 2.5, 3.5 };
    const double lam_h3_t[11] = { -15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15 };
    const double lam_h3_c[11] = { -13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13 };
    const double lam_h4_c[5]  = { -2, -1, 0, 1, 2 };

    ChainSpec treat[4], ctrl[4];
    init_chain_from_spec(&treat[0], "H1_treat_7x7_345", 7, lam_h1_t);
    init_chain_from_spec(&ctrl[0],  "H1_ctrl_7x7_125",  7, lam_h1_c);
    init_chain_from_spec(&treat[1], "H2_treat_8x8_m1",  8, lam_h2_t);
    init_chain_from_spec(&ctrl[1],  "H2_ctrl_6x6_157",  6, lam_h2_c);
    init_chain_from_spec(&treat[2], "H3_treat_11x11_m6", 11, lam_h3_t);
    init_chain_from_spec(&ctrl[2],  "H3_ctrl_11x11_m5",  11, lam_h3_c);
    init_chain_j14(&treat[3]);
    init_chain_from_spec(&ctrl[3],  "H4_ctrl_5x5_kraw", 5, lam_h4_c);

    /* 1. Verify QGTL Theorem 10 Fubini-Study metric velocity g_{tt} == b_0^2 on all 4 ESE chains! */
    printf("[QGTL] Verifying Theorem 10 Fubini-Study Metric Velocity g_{tt} == b_0^2 via vendored QGTL:\n");
    double qgtl_gtt[4], qgtl_dfs[4], qgtl_eta[4];
    for (int h = 0; h < 4; ++h) {
        if (verify_qgtl_geometry(&treat[h], &qgtl_gtt[h], &qgtl_dfs[h], &qgtl_eta[h]) != 0) {
            fprintf(stderr, "[QGTL] Engine error on arm %d\n", h);
            return 10;
        }
        double rel_err = fabs(qgtl_gtt[h] - treat[h].b0 * treat[h].b0) / (treat[h].b0 * treat[h].b0);
        printf("  %-18s: g_tt=%.6f, b0^2=%.6f (rel_err=%.2e), d_FS(0,tau)=%.6f (pi/2=%.6f), eta=%.4f\n",
               treat[h].name, qgtl_gtt[h], treat[h].b0 * treat[h].b0, rel_err,
               qgtl_dfs[h], M_PI / 2.0, qgtl_eta[h]);
        if (rel_err > 1e-4 || fabs(qgtl_dfs[h] - M_PI / 2.0) > 1e-4 || qgtl_eta[h] > 1.0 + 1e-9) {
            fprintf(stderr, "[QGTL] Theorem 10 check failed on arm %d!\n", h);
            return 11;
        }
    }

    /* 2. Run Pre-Registered 30-Seed QRNG Diagonal Disorder Study (PREREGISTRATION.md) */
    const double eps_list[5] = { 0.00, 0.01, 0.02, 0.05, 0.10 };
    const int n_seeds = 30;
    const char *h_ids[4] = { "H1", "H2", "H3", "H4" };

    FILE *fp = fopen(json_path, "wb");
    if (!fp) {
        fprintf(stderr, "Failed to open output JSON: %s\n", json_path);
        return 12;
    }

    fprintf(fp, "{\n");
    fprintf(fp, "  \"preregistration\": \"PREREGISTRATION.md\",\n");
    fprintf(fp, "  \"qrng_version\": \"%s\",\n", qrng_version());
    fprintf(fp, "  \"n_seeds\": %d,\n", n_seeds);
    fprintf(fp, "  \"epsilons\": [0.00, 0.01, 0.02, 0.05, 0.10],\n");
    fprintf(fp, "  \"qgtl_theorem10\": [\n");
    for (int h = 0; h < 4; ++h) {
        fprintf(fp, "    {\"arm\": \"%s\", \"name\": \"%s\", \"b0_sq\": %.12f, \"qgtl_gtt\": %.12f, \"qgtl_dfs_ese\": %.12f, \"tau_ese\": %.12f, \"eta\": %.12f}%s\n",
                h_ids[h], treat[h].name, treat[h].b0 * treat[h].b0, qgtl_gtt[h], qgtl_dfs[h],
                treat[h].tau_ideal, qgtl_eta[h], (h < 3 ? "," : ""));
    }
    fprintf(fp, "  ],\n");
    fprintf(fp, "  \"arms\": [\n");

    for (int h = 0; h < 4; ++h) {
        fprintf(fp, "    {\n");
        fprintf(fp, "      \"id\": \"%s\",\n", h_ids[h]);
        fprintf(fp, "      \"treat_name\": \"%s\", \"treat_n\": %zu, \"treat_b_mean\": %.12f,\n",
                treat[h].name, treat[h].n, treat[h].b_mean);
        fprintf(fp, "      \"ctrl_name\": \"%s\", \"ctrl_n\": %zu, \"ctrl_b_mean\": %.12f,\n",
                ctrl[h].name, ctrl[h].n, ctrl[h].b_mean);
        fprintf(fp, "      \"levels\": [\n");
        for (int ei = 0; ei < 5; ++ei) {
            double eps = eps_list[ei];
            fprintf(fp, "        {\"eps\": %.2f, \"treat_min\": [", eps);
            double t_mins[30], c_mins[30], t_taus[30];
            for (int s = 1; s <= n_seeds; ++s) {
                /* Deterministic seed tag bound to (hypothesis, eps_idx, seed) */
                uint8_t seed_buf[32];
                memset(seed_buf, 0, sizeof(seed_buf));
                snprintf((char *)seed_buf, sizeof(seed_buf), "SE2026-%s-E%d-S%02d", h_ids[h], ei, s);
                qrng_ctx *qctx = NULL;
                if (qrng_init(&qctx, seed_buf, sizeof(seed_buf)) != QRNG_SUCCESS) {
                    fprintf(stderr, "qrng_init failed\n");
                    return 13;
                }
                double xi[16];
                for (int k = 0; k < 16; ++k) {
                    xi[k] = 2.0 * qrng_double(qctx) - 1.0; /* Uniform(-1, 1) */
                }
                qrng_free(qctx);

                double a_t[16], a_c[16], ev_t[16], v0_t[16], ev_c[16], v0_c[16];
                for (size_t k = 0; k < treat[h].n; ++k) a_t[k] = treat[h].a[k] + eps * treat[h].b_mean * xi[k];
                for (size_t k = 0; k < ctrl[h].n; ++k)  a_c[k] = ctrl[h].a[k] + eps * ctrl[h].b_mean * xi[k];
                tridiag_ql_c(treat[h].n, a_t, treat[h].b, ev_t, v0_t);
                tridiag_ql_c(ctrl[h].n,  a_c, ctrl[h].b,  ev_c, v0_c);
                t_mins[s - 1] = compute_interior_min(treat[h].n, ev_t, v0_t, M_PI, &t_taus[s - 1]);
                double dummy_tau = 0.0;
                c_mins[s - 1] = compute_interior_min(ctrl[h].n, ev_c, v0_c, M_PI, &dummy_tau);
            }
            for (int i = 0; i < n_seeds; ++i) fprintf(fp, "%.10f%s", t_mins[i], (i + 1 < n_seeds ? ", " : ""));
            fprintf(fp, "], \"ctrl_min\": [");
            for (int i = 0; i < n_seeds; ++i) fprintf(fp, "%.10f%s", c_mins[i], (i + 1 < n_seeds ? ", " : ""));
            fprintf(fp, "], \"treat_tau\": [");
            for (int i = 0; i < n_seeds; ++i) fprintf(fp, "%.10f%s", t_taus[i], (i + 1 < n_seeds ? ", " : ""));
            fprintf(fp, "]}%s\n", (ei < 4 ? "," : ""));

            if (ei == 3) { /* eps = 0.05 primary endpoint summary */
                double mt = 0.0, mc = 0.0;
                for (int i = 0; i < n_seeds; ++i) { mt += t_mins[i]; mc += c_mins[i]; }
                printf("[QRNG] %s (eps=0.05, K=30): mean treat_min=%.6f vs ctrl_min=%.6f (diff=%.6f)\n",
                       h_ids[h], mt / n_seeds, mc / n_seeds, (mc - mt) / n_seeds);
            }
        }
        fprintf(fp, "      ]\n");
        fprintf(fp, "    }%s\n", (h < 3 ? "," : ""));
    }
    fprintf(fp, "  ]\n");
    fprintf(fp, "}\n");
    fclose(fp);
    printf("[QGTL+QRNG] Wrote %s successfully (0 errors).\n", json_path);
    return 0;
}
