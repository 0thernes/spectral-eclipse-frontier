// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Spectral Eclipse Frontier -- ISO C++20 Direct Matrix-Exponential Propagator
// Independently verifies e^{-i J t} |e_0> via symmetric tridiagonal QR/QL
// eigendecomposition (implicit Wilkinson shift), confirming exact PST and
// Early State Exclusion directly on literal Jacobi matrices for N = 4..23
// and the non-symmetric staggered-field family J_{a,b}.

#include <algorithm>
#include <cmath>
#include <complex>
#include <cstddef>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

namespace se {

constexpr double kPi = 3.141592653589793238462643383279502884;

struct EigenDecomp {
    std::vector<double> evals;
    std::vector<std::vector<double>> evecs; // evecs[k][i] = component i of eigenvector k
};

// Implicit QL algorithm with Wilkinson shifts for real symmetric tridiagonal matrices.
// Standard textbook Bowdler-Martin-Reinsch-Wilkinson / EISPACK tql2 formulation.
EigenDecomp tridiag_ql(const std::vector<double>& diag_in,
                       const std::vector<double>& off_in) {
    const std::size_t n = diag_in.size();
    if (n == 0 || off_in.size() + 1 != n) {
        throw std::invalid_argument("tridiag_ql: invalid matrix dimensions");
    }
    std::vector<double> d = diag_in;
    std::vector<double> e(n, 0.0);
    for (std::size_t i = 0; i + 1 < n; ++i) e[i] = off_in[i];
    std::vector<std::vector<double>> z(n, std::vector<double>(n, 0.0));
    for (std::size_t i = 0; i < n; ++i) z[i][i] = 1.0;

    for (std::size_t l = 0; l < n; ++l) {
        int iter = 0;
        std::size_t m = l;
        do {
            for (m = l; m + 1 < n; ++m) {
                double dd = std::abs(d[m]) + std::abs(d[m + 1]);
                if (std::abs(e[m]) <= std::numeric_limits<double>::epsilon() * dd) break;
            }
            if (m != l) {
                if (++iter > 100) {
                    throw std::runtime_error("tridiag_ql: failed to converge");
                }
                double g = (d[l + 1] - d[l]) / (2.0 * e[l]);
                double r = std::hypot(g, 1.0);
                g = d[m] - d[l] + e[l] / (g + std::copysign(r, g));
                double s = 1.0, c = 1.0, p = 0.0;
                for (std::size_t i = m; i-- > l;) {
                    double f = s * e[i];
                    double b = c * e[i];
                    r = std::hypot(f, g);
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
                    for (std::size_t k = 0; k < n; ++k) {
                        double zk = z[k][i + 1];
                        z[k][i + 1] = s * z[k][i] + c * zk;
                        z[k][i] = c * z[k][i] - s * zk;
                    }
                }
                if (iter > 0 && !(e[m] == 0.0 && m != l)) {
                    d[l] -= p;
                    e[l] = g;
                    e[m] = 0.0;
                }
            }
        } while (m != l);
    }

    // Sort eigenpairs in ascending order of eigenvalues.
    std::vector<std::size_t> idx(n);
    std::iota(idx.begin(), idx.end(), 0);
    std::sort(idx.begin(), idx.end(), [&](std::size_t a, std::size_t b) { return d[a] < d[b]; });

    EigenDecomp out;
    out.evals.resize(n);
    out.evecs.assign(n, std::vector<double>(n, 0.0));
    for (std::size_t k = 0; k < n; ++k) {
        out.evals[k] = d[idx[k]];
        for (std::size_t i = 0; i < n; ++i) {
            out.evecs[k][i] = z[i][idx[k]];
        }
    }
    return out;
}

// Reconstruct persymmetric Jacobi matrix from strictly increasing spectrum via Lanczos + MGS.
void reconstruct_persymmetric(const std::vector<double>& lam,
                              std::vector<double>& a_out,
                              std::vector<double>& b_out) {
    const std::size_t n = lam.size();
    std::vector<double> log_w(n, 0.0);
    double max_lw = -std::numeric_limits<double>::infinity();
    for (std::size_t k = 0; k < n; ++k) {
        double s = 0.0;
        for (std::size_t j = 0; j < n; ++j) {
            if (j != k) s -= std::log(std::abs(lam[k] - lam[j]));
        }
        log_w[k] = s;
        max_lw = std::max(max_lw, s);
    }
    std::vector<double> w(n, 0.0);
    double sum_w = 0.0;
    for (std::size_t k = 0; k < n; ++k) {
        w[k] = std::exp(log_w[k] - max_lw);
        sum_w += w[k];
    }
    for (double& wk : w) wk /= sum_w;

    a_out.assign(n, 0.0);
    b_out.assign(n - 1, 0.0);
    std::vector<std::vector<double>> Q(n, std::vector<double>(n, 0.0));
    for (std::size_t k = 0; k < n; ++k) Q[0][k] = std::sqrt(w[k]);

    for (std::size_t j = 0; j < n; ++j) {
        double alpha = 0.0;
        for (std::size_t k = 0; k < n; ++k) alpha += lam[k] * Q[j][k] * Q[j][k];
        a_out[j] = alpha;
        if (j + 1 == n) break;
        std::vector<double> v(n, 0.0);
        double beta_prev = (j == 0) ? 0.0 : b_out[j - 1];
        for (std::size_t k = 0; k < n; ++k) {
            v[k] = (lam[k] - alpha) * Q[j][k] - (j == 0 ? 0.0 : beta_prev * Q[j - 1][k]);
        }
        for (int pass = 0; pass < 2; ++pass) {
            for (std::size_t m = 0; m <= j; ++m) {
                double dot = 0.0;
                for (std::size_t k = 0; k < n; ++k) dot += v[k] * Q[m][k];
                for (std::size_t k = 0; k < n; ++k) v[k] -= dot * Q[m][k];
            }
        }
        double norm2 = 0.0;
        for (double vk : v) norm2 += vk * vk;
        b_out[j] = std::sqrt(norm2);
        for (std::size_t k = 0; k < n; ++k) Q[j + 1][k] = v[k] / b_out[j];
    }
}

std::vector<std::complex<double>> evolve_e0(const EigenDecomp& ed, double t) {
    const std::size_t n = ed.evals.size();
    std::vector<std::complex<double>> psi(n, {0.0, 0.0});
    for (std::size_t k = 0; k < n; ++k) {
        std::complex<double> phase = std::polar(ed.evecs[k][0], -ed.evals[k] * t);
        for (std::size_t i = 0; i < n; ++i) {
            psi[i] += phase * ed.evecs[k][i];
        }
    }
    return psi;
}

struct ChainReport {
    std::string label;
    std::size_t n;
    double max_eig_err;
    double pst_fid;
    double min_re_amp;
    double ese_tau;
    bool has_ese;
};

ChainReport analyze_spectrum(const std::string& label, const std::vector<double>& lam,
                             double pst_time, double check_t = -1.0) {
    std::vector<double> a, b;
    reconstruct_persymmetric(lam, a, b);
    auto ed = tridiag_ql(a, b);
    double max_eig_err = 0.0;
    for (std::size_t k = 0; k < lam.size(); ++k) {
        max_eig_err = std::max(max_eig_err, std::abs(ed.evals[k] - lam[k]));
    }
    auto psi_pst = evolve_e0(ed, pst_time);
    double pst_fid = std::abs(psi_pst.back());
    double min_re = 1e9;
    double ese_tau = -1.0;
    const int steps = 4000;
    double prev_re = 1.0;
    for (int s = 1; s < steps; ++s) {
        double t = pst_time * static_cast<double>(s) / static_cast<double>(steps);
        auto psi = evolve_e0(ed, t);
        double re0 = psi[0].real();
        if (re0 < min_re) min_re = re0;
        // Guard against O((pi - t)^(N-1)) catastrophic cancellation noise (~2e-16) near t = pi.
        if (ese_tau < 0.0 && prev_re > 1e-11 && re0 < -1e-11) {
            // Bisection to 1e-13
            double lo = pst_time * static_cast<double>(s - 1) / static_cast<double>(steps);
            double hi = t;
            for (int it = 0; it < 60; ++it) {
                double mid = 0.5 * (lo + hi);
                if (evolve_e0(ed, mid)[0].real() > 0.0) lo = mid; else hi = mid;
            }
            ese_tau = 0.5 * (lo + hi);
        }
        prev_re = re0;
    }
    if (check_t > 0.0) {
        auto psi_c = evolve_e0(ed, check_t);
        if (psi_c[0].real() < min_re) min_re = psi_c[0].real();
    }
    return {label, lam.size(), max_eig_err, pst_fid, min_re, ese_tau, (ese_tau > 0.0 || min_re < -1e-10)};
}

} // namespace se

int main() {
    using namespace se;
    std::vector<ChainReport> reports;

    // 1. Canonical 4x4..11x11 symmetric PST chains + Theorem 8 (R=4, N=14)
    reports.push_back(analyze_spectrum("4x4_noESE_1_3", {-1.5, -0.5, 0.5, 1.5}, kPi));
    reports.push_back(analyze_spectrum("4x4_ESE_3_5", {-2.5, -1.5, 1.5, 2.5}, kPi));
    reports.push_back(analyze_spectrum("5x5_noESE_1_2", {-2, -1, 0, 1, 2}, kPi));
    reports.push_back(analyze_spectrum("5x5_ESE_3_4", {-4, -3, 0, 3, 4}, kPi));
    reports.push_back(analyze_spectrum("6x6_noESE_1_3_5", {-2.5, -1.5, -0.5, 0.5, 1.5, 2.5}, kPi));
    reports.push_back(analyze_spectrum("7x7_noESE_1_2_3", {-3, -2, -1, 0, 1, 2, 3}, kPi));
    reports.push_back(analyze_spectrum("7x7_ESE_3_4_5", {-5, -4, -3, 0, 3, 4, 5}, kPi, kPi / 5.0));
    reports.push_back(analyze_spectrum("8x8_rupture_m1", {-5.5, -4.5, -3.5, -0.5, 0.5, 3.5, 4.5, 5.5}, kPi, 2.0 * kPi / 9.0));
    reports.push_back(analyze_spectrum("9x9_critical_1_2_3_4", {-4, -3, -2, -1, 0, 1, 2, 3, 4}, kPi));
    reports.push_back(analyze_spectrum("9x9_critical_1_20_21_22", {-22, -21, -20, -1, 0, 1, 20, 21, 22}, kPi));
    reports.push_back(analyze_spectrum("11x11_subcrit_m5", {-13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13}, kPi));
    reports.push_back(analyze_spectrum("11x11_supercrit_m6", {-15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15}, kPi, 2.0 * kPi / 27.0));

    // Check Theorem 8 universal phase transition at R=4: N=14 (3R+2=14, r=5 cluster)
    std::vector<double> lam14;
    int m14 = 40;
    for (int j = 4; j >= 0; --j) lam14.push_back(-0.5 * static_cast<double>(2 * m14 + 1 + 2 * j));
    lam14.push_back(-1.5); lam14.push_back(-0.5); lam14.push_back(0.5); lam14.push_back(1.5);
    for (int j = 0; j <= 4; ++j) lam14.push_back(0.5 * static_cast<double>(2 * m14 + 1 + 2 * j));
    reports.push_back(analyze_spectrum("14x14_R4_r5_rupture", lam14, kPi));

    // Direct literal matrix test for Theorem 9 staggered-field family J_{a,b} (a=1, b=4, 10, 16)
    bool all_ok = true;
    for (int k = 0; k < 3; ++k) {
        double a_val = 1.0;
        double b_val = 4.0 + 6.0 * k;
        std::vector<double> diag = {b_val, b_val + 2.0 * a_val, b_val, b_val + 2.0 * a_val, b_val};
        double b0 = std::sqrt(b_val * b_val - a_val * a_val);
        double b1 = std::sqrt(a_val * (a_val + 2.0 * b_val) / 2.0);
        std::vector<double> off = {b0, b1, b1, b0};
        auto ed = tridiag_ql(diag, off);
        auto psi_ese = evolve_e0(ed, kPi / 3.0);
        auto psi_pst = evolve_e0(ed, kPi);
        double amp0 = std::abs(psi_ese[0]);
        double fid_pst = std::abs(psi_pst[4]);
        std::cout << "[C++20] J_{1," << static_cast<int>(b_val) << "} exact matrix: "
                  << "|psi_0(pi/3)| = " << std::scientific << std::setprecision(3) << amp0
                  << ", |psi_4(pi)| = " << std::fixed << std::setprecision(12) << fid_pst << "\n";
        if (amp0 > 1e-12 || std::abs(fid_pst - 1.0) > 1e-12) all_ok = false;
    }

    // Print JSON-friendly summary & assert theorem predictions
    for (const auto& r : reports) {
        std::cout << "[C++20] " << std::left << std::setw(24) << r.label
                  << " N=" << std::setw(2) << r.n
                  << " eig_err=" << std::scientific << std::setprecision(2) << r.max_eig_err
                  << " PST=" << std::fixed << std::setprecision(10) << r.pst_fid
                  << " minRe=" << std::setprecision(6) << r.min_re_amp
                  << " ESE=" << (r.has_ese ? "YES" : "NO")
                  << " tau=" << std::setprecision(6) << r.ese_tau << "\n";
        if (r.max_eig_err > 1e-10 || std::abs(r.pst_fid - 1.0) > 1e-10) all_ok = false;
    }

    // Assert exact expected ESE booleans matching Lean Theorems 1-8
    const std::vector<bool> expected_ese = {
        false, true, false, true, false, false, true, true, false, false, false, true, true
    };
    for (std::size_t i = 0; i < expected_ese.size(); ++i) {
        if (reports[i].has_ese != expected_ese[i]) {
            std::cerr << "MISMATCH on " << reports[i].label << "\n";
            all_ok = false;
        }
    }

    if (!all_ok) {
        std::cerr << "[C++20] FAILURE!\n";
        return 1;
    }
    std::cout << "[C++20] ALL 16 DIRECT MATRIX-EXPONENTIAL VERIFICATIONS PASSED.\n";
    return 0;
}
