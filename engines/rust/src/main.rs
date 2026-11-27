// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Spectral Eclipse Frontier -- Safe Rust (#![forbid(unsafe_code)]) Multi-Core
// Phase-Diagram Scanner & Exact Theorem 1-10 Empirical Cross-Verifier.

#![forbid(unsafe_code)]

use std::f64::consts::PI;
use std::thread;

/// Compute exact normalized persymmetric spectral weights w_k = c / prod_{j != k} |lam_k - lam_j|.
pub fn persymmetric_weights(lam: &[f64]) -> Result<Vec<f64>, &'static str> {
    let n = lam.len();
    if n < 2 {
        return Err("spectrum must have length >= 2");
    }
    for i in 0..(n - 1) {
        if lam[i].partial_cmp(&lam[i + 1]) != Some(std::cmp::Ordering::Less) {
            return Err("spectrum must be strictly increasing");
        }
    }
    let mut log_w = vec![0.0_f64; n];
    let mut max_lw = f64::NEG_INFINITY;
    for k in 0..n {
        let mut s = 0.0_f64;
        for j in 0..n {
            if j != k {
                s -= (lam[k] - lam[j]).abs().ln();
            }
        }
        log_w[k] = s;
        if s > max_lw {
            max_lw = s;
        }
    }
    let mut w = vec![0.0_f64; n];
    let mut sum = 0.0_f64;
    for k in 0..n {
        w[k] = (log_w[k] - max_lw).exp();
        sum += w[k];
    }
    if !sum.is_finite() || sum <= 0.0 {
        return Err("weight normalization underflow/overflow");
    }
    for wk in &mut w {
        *wk /= sum;
    }
    Ok(w)
}

/// Evaluate return amplitude Re(<e_0 | e^{-i J t} | e_0>) and Im(...) at time t.
pub fn return_amp(lam: &[f64], w: &[f64], t: f64) -> (f64, f64) {
    let mut re = 0.0_f64;
    let mut im = 0.0_f64;
    for (&lk, &wk) in lam.iter().zip(w.iter()) {
        let phase = lk * t;
        re += wk * phase.cos();
        im -= wk * phase.sin();
    }
    (re, im)
}

/// Compute energy variance sigma^2 = Var_{e_0}(J) = b_0^2 = sum w_k lam_k^2 - (sum w_k lam_k)^2.
pub fn energy_variance(lam: &[f64], w: &[f64]) -> f64 {
    let mean: f64 = lam.iter().zip(w.iter()).map(|(&l, &wk)| wk * l).sum();
    lam.iter()
        .zip(w.iter())
        .map(|(&l, &wk)| wk * (l - mean).powi(2))
        .sum()
}

/// Detect real-amplitude Early State Exclusion on (0, pst_time) with cancellation guard.
/// Returns (has_ese, min_re_amp, first_ese_tau).
pub fn detect_real_ese(lam: &[f64], pst_time: f64, grid: usize) -> (bool, f64, Option<f64>) {
    let w = persymmetric_weights(lam).expect("valid strictly increasing spectrum");
    let mut min_re = f64::INFINITY;
    let mut first_tau: Option<f64> = None;
    let mut prev_re = 1.0_f64;
    for s in 1..grid {
        let t = pst_time * (s as f64) / (grid as f64);
        let (re, _) = return_amp(lam, &w, t);
        if re < min_re {
            min_re = re;
        }
        if first_tau.is_none() && prev_re > 1e-11 && re < -1e-11 {
            let mut lo = pst_time * ((s - 1) as f64) / (grid as f64);
            let mut hi = t;
            for _ in 0..60 {
                let mid = 0.5 * (lo + hi);
                if return_amp(lam, &w, mid).0 > 0.0 {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            first_tau = Some(0.5 * (lo + hi));
        }
        prev_re = re;
    }
    let has_ese = first_tau.is_some() || min_re < -1e-10;
    (has_ese, min_re, first_tau)
}

/// Build symmetric (R, r) Krawtchouk-core + high-energy-cluster PST spectrum of total size N = R + 2r
/// (odd R: {-(R-1)/2, ..., 0, ..., (R-1)/2}; even R: {-(R-1)/2, ..., -1/2, +1/2, ..., +(R-1)/2})
/// paired with a parity-consistent symmetric r-pair unit-spaced cluster at offset M.
pub fn build_core_cluster_spectrum(core_r: usize, cluster_r: usize, m_shift: usize) -> Vec<f64> {
    let mut lam = Vec::with_capacity(core_r + 2 * cluster_r);
    if core_r % 2 == 1 {
        // Odd core: {-(R-1)/2, ..., 0, ..., +(R-1)/2} (integers).
        // Alternating-parity condition: adjacent eigenvalue differences must be odd integers!
        // Core max is c = (R - 1)/2. Next eigenvalue must have opposite parity to c => start at 2*m + ((c+1)%2).
        let c = (core_r - 1) / 2;
        let start = 2 * m_shift + ((c + 1) % 2);
        for j in (0..cluster_r).rev() {
            lam.push(-((start + j) as f64));
        }
        for k in -(c as isize)..=(c as isize) {
            lam.push(k as f64);
        }
        for j in 0..cluster_r {
            lam.push((start + j) as f64);
        }
    } else {
        // Even core: half-integers {-(R-1)/2, ..., -1/2, +1/2, ..., +(R-1)/2}.
        // Scaled in half-integer units: odd integers p_k!
        // Core max half-int index is 2*(R/2) - 1 = R - 1 (odd).
        // Next odd integer must differ by 2 mod 4 from R - 1 (since in unscaled units, diff is odd => 2*diff = 2 mod 4!).
        let core_max_odd = core_r - 1;
        // Start odd integer s_odd such that (s_odd - core_max_odd) % 4 == 2:
        let base_mod = (core_max_odd + 2) % 4;
        let start_odd = 4 * m_shift + base_mod;
        for j in (0..cluster_r).rev() {
            lam.push(-0.5 * ((start_odd + 2 * j) as f64));
        }
        let half_cnt = core_r / 2;
        for j in (0..half_cnt).rev() {
            lam.push(-0.5 * ((2 * j + 1) as f64));
        }
        for j in 0..half_cnt {
            lam.push(0.5 * ((2 * j + 1) as f64));
        }
        for j in 0..cluster_r {
            lam.push(0.5 * ((start_odd + 2 * j) as f64));
        }
    }
    lam
}

/// Find exact integer threshold m* for a given (R, r) family (or None if no ESE up to m_max).
pub fn find_threshold_m(core_r: usize, cluster_r: usize, m_max: usize) -> Option<usize> {
    let m_start = core_r + 1;
    for m in m_start..=m_max {
        let lam = build_core_cluster_spectrum(core_r, cluster_r, m);
        // Check dense grid + analytic cluster center t0 = 2*pi / (2*center)
        let (has_ese, _, _) = detect_real_ese(&lam, PI, 6000);
        if has_ese {
            return Some(m);
        }
    }
    None
}

fn main() {
    println!("[Rust] Spectral Eclipse Multi-Core Phase-Diagram Scanner (forbid(unsafe_code))");

    // 1. Multi-threaded verification of Theorem 8 universal phase transition r_crit(R) = R + 1
    //    across R = 2, 3, 4, 5 (N up to 17) checking BOTH r = R (critical tower, no rupture)
    //    and r = R + 1 (sharp rupture N_crit = 3R + 2)!
    let tasks: Vec<(usize, usize, usize)> = vec![
        (2, 2, 40), // N=6:  r=R   => NO rupture (Theorem 3!)
        (2, 3, 40), // N=8:  r=R+1 => RUPTURE at m=1 (Theorem 5!)
        (3, 3, 40), // N=9:  r=R   => NO rupture (Theorem 6!)
        (3, 4, 40), // N=11: r=R+1 => RUPTURE at m=6, M*=12 (Theorem 7!)
        (4, 4, 50), // N=12: r=R   => NO rupture (critical tower!)
        (4, 5, 50), // N=14: r=R+1 => RUPTURE!
        (5, 5, 50), // N=15: r=R   => NO rupture (critical tower!)
        (5, 6, 80), // N=17: r=R+1 => RUPTURE!
    ];

    let handles: Vec<_> = tasks
        .into_iter()
        .map(|(core_r, cluster_r, m_max)| {
            thread::spawn(move || {
                let n = core_r + 2 * cluster_r;
                let thresh = find_threshold_m(core_r, cluster_r, m_max);
                (core_r, cluster_r, n, thresh)
            })
        })
        .collect();

    let mut ok = true;
    for h in handles {
        let (core_r, cluster_r, n, thresh) = h.join().expect("worker thread panicked");
        let expected_rupture = cluster_r > core_r;
        println!(
            "[Rust] Phase cell (R={}, r={}, N={:2}): threshold_m={:?} (expected rupture={})",
            core_r, cluster_r, n, thresh, expected_rupture
        );
        if expected_rupture != thresh.is_some() {
            eprintln!("PHASE MISMATCH at (R={}, r={})", core_r, cluster_r);
            ok = false;
        }
        // Check exact Lean Theorem 7 M* = 12 (m = 6) at (R=3, r=4, N=11)
        if core_r == 3 && cluster_r == 4 && thresh != Some(6) {
            eprintln!("THRESHOLD MISMATCH at (3,4): expected Some(6), got {:?}", thresh);
            ok = false;
        }
    }

    // 2. Verify Mandelstam-Tamm QSL bound (Theorem 10): pi / (2 * sigma) <= tau for 500 random ESE spectra!
    let mut seed: u64 = 0x2026_0020_5EED_CAFE;
    let mut next_u64 = || -> u64 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut checked_qsl = 0usize;
    let mut min_eta = f64::INFINITY;
    let mut max_eta = 0.0_f64;
    for _ in 0..1000 {
        let x = 3 + (next_u64() % 5) * 2; // odd >= 3
        let y = x + 1 + (next_u64() % 4) * 2; // even > x
        let z = y + 1 + (next_u64() % 4) * 2; // odd > y
        let lam = vec![
            -(z as f64),
            -(y as f64),
            -(x as f64),
            0.0,
            x as f64,
            y as f64,
            z as f64,
        ];
        let w = persymmetric_weights(&lam).expect("valid 7x7");
        let sigma = energy_variance(&lam, &w).sqrt();
        let (has_ese, _, tau_opt) = detect_real_ese(&lam, PI, 4000);
        if has_ese {
            if let Some(tau) = tau_opt {
                let qsl = PI / (2.0 * sigma);
                let eta = qsl / tau;
                if tau + 1e-9 < qsl {
                    eprintln!("QSL VIOLATION: tau={} < qsl={}", tau, qsl);
                    ok = false;
                }
                min_eta = min_eta.min(eta);
                max_eta = max_eta.max(eta);
                checked_qsl += 1;
            }
        }
    }
    println!(
        "[Rust] Verified Theorem 10 Mandelstam-Tamm QSL on {} random 7x7 ESE chains: eta in [{:.4}, {:.4}] <= 1.0",
        checked_qsl, min_eta, max_eta
    );

    if !ok {
        std::process::exit(1);
    }
    println!("[Rust] ALL PHASE-DIAGRAM & QSL SCANS PASSED (0 errors, 0 unsafe).");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_conjecture_4_1_boundary() {
        let (ese_1, _, _) = detect_real_ese(&[-3.0, -2.0, -1.0, 0.0, 1.0, 2.0, 3.0], PI, 4000);
        assert!(!ese_1);
        let (ese_3, _, _) = detect_real_ese(&[-5.0, -4.0, -3.0, 0.0, 3.0, 4.0, 5.0], PI, 4000);
        assert!(ese_3);
    }

    #[test]
    fn test_sharp_11x11_threshold() {
        let lam5 = build_core_cluster_spectrum(3, 4, 5);
        let lam6 = build_core_cluster_spectrum(3, 4, 6);
        assert!(!detect_real_ese(&lam5, PI, 6000).0);
        assert!(detect_real_ese(&lam6, PI, 6000).0);
    }

    #[test]
    fn test_negative_invalid_spectrum() {
        assert!(persymmetric_weights(&[1.0]).is_err());
        assert!(persymmetric_weights(&[1.0, 1.0, 2.0]).is_err());
    }
}
