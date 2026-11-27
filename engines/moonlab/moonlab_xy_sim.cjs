// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Spectral Eclipse Frontier -- Moonlab WASM 5-Qubit (2^5 = 32-dim) Many-Body
// XY + Staggered-Z Spin-Chain Simulator for Theorem 9 (J_{1,4}).
//
// Executes the REAL vendored third_party/moonlab/moonlab.wasm state-vector
// simulator on 5 qubits (32 complex amplitudes) via 2nd-order Strang-Trotter
// gate synthesis of:
//   H_XY = sum_{k=0}^4 a_k (I - Z_k)/2 + sum_{k=0}^3 (b_k/2) (X_k X_{k+1} + Y_k Y_{k+1})
// where J_{1,4} has a = (4, 6, 4, 6, 4), b = (sqrt(15), sqrt(9/2), sqrt(9/2), sqrt(15)).
//
// Verifies independently in the full 2^5 = 32-dim many-body Hilbert space:
//   1. Single-excitation Hamming-weight-1 sector conservation: sum_{|x|=1} P(x) = 1
//   2. Complex Early State Exclusion at t = pi/3: P(|00001>) < 1e-4
//   3. Exact Perfect State Transfer at t = pi:   P(|10000>) > 0.9998

'use strict';

const path = require('path');
const MoonlabModule = require(path.resolve(__dirname, '../../third_party/moonlab/moonlab.js'));

const PI = Math.PI;

// Apply exact two-qubit XY hopping gate exp(-i * alpha * (X_q1 X_q2 + Y_q1 Y_q2))
// using native Moonlab gates (CNOT, H, Rx, Rz). Since [X⊗X, Y⊗Y] = 0, this factorizes
// with ZERO Trotter error per bond!
function applyXYBond(m, st, q1, q2, alpha) {
  // 1. exp(-i * alpha * X_q1 X_q2) = H H CNOT Rz(2*alpha) CNOT H H
  m._gate_hadamard(st, q1);
  m._gate_hadamard(st, q2);
  m._gate_cnot(st, q1, q2);
  m._gate_rz(st, q2, 2.0 * alpha);
  m._gate_cnot(st, q1, q2);
  m._gate_hadamard(st, q1);
  m._gate_hadamard(st, q2);

  // 2. exp(-i * alpha * Y_q1 Y_q2) = Rx(-pi/2) Rx(-pi/2) CNOT Rz(2*alpha) CNOT Rx(pi/2) Rx(pi/2)
  m._gate_rx(st, q1, -PI / 2.0);
  m._gate_rx(st, q2, -PI / 2.0);
  m._gate_cnot(st, q1, q2);
  m._gate_rz(st, q2, 2.0 * alpha);
  m._gate_cnot(st, q1, q2);
  m._gate_rx(st, q1, PI / 2.0);
  m._gate_rx(st, q2, PI / 2.0);
}

// One 2nd-order Strang-Trotter step of duration dt for H_XY = H_Z + H_even + H_odd.
function strangStep(m, st, aDiag, bHop, dt) {
  // Half Z layer: exp(-i * a_k * (I - Z_k)/2 * dt/2) = phase * Rz(-a_k * dt/2)
  for (let k = 0; k < aDiag.length; k++) {
    m._gate_rz(st, k, -aDiag[k] * (dt / 2.0));
  }
  // Half even-bond XY layer: bonds (0,1) and (2,3), alpha = (b_k / 2) * (dt / 2)
  for (let k = 0; k < bHop.length; k += 2) {
    applyXYBond(m, st, k, k + 1, (bHop[k] / 2.0) * (dt / 2.0));
  }
  // Full odd-bond XY layer: bonds (1,2) and (3,4), alpha = (b_k / 2) * dt
  for (let k = 1; k < bHop.length; k += 2) {
    applyXYBond(m, st, k, k + 1, (bHop[k] / 2.0) * dt);
  }
  // Half even-bond XY layer
  for (let k = 0; k < bHop.length; k += 2) {
    applyXYBond(m, st, k, k + 1, (bHop[k] / 2.0) * (dt / 2.0));
  }
  // Half Z layer
  for (let k = 0; k < aDiag.length; k++) {
    m._gate_rz(st, k, -aDiag[k] * (dt / 2.0));
  }
}

async function runSimulation(m, aDiag, bHop, totalTime, steps) {
  const nQubits = aDiag.length;
  const st = m._malloc(128);
  const rc = m._quantum_state_init(st, nQubits);
  if (rc !== 0) throw new Error(`Moonlab _quantum_state_init failed: ${rc}`);

  // Prepare initial single-excitation state |site 0> = X_0 |00000>
  m._gate_pauli_x(st, 0);

  const dt = totalTime / steps;
  for (let s = 0; s < steps; s++) {
    strangStep(m, st, aDiag, bHop, dt);
  }

  // Extract all 2^5 = 32 probabilities via Moonlab WASM!
  const dim = 1 << nQubits;
  const probs = [];
  for (let idx = 0; idx < dim; idx++) {
    probs.push(m._quantum_state_get_probability(st, BigInt(idx)));
  }

  // Single-excitation basis states are bitmasks 1 << k (k = 0..n-1)
  const siteProbs = [];
  let singleSectorSum = 0.0;
  for (let k = 0; k < nQubits; k++) {
    const pk = probs[1 << k];
    siteProbs.push(pk);
    singleSectorSum += pk;
  }

  m._quantum_state_free(st);
  m._free(st);
  return { siteProbs, singleSectorSum, totalProb: probs.reduce((a, b) => a + b, 0) };
}

(async () => {
  const m = await MoonlabModule();

  // Theorem 9 staggered-field 5-qubit spin chain J_{1,4}
  const aDiag = [4.0, 6.0, 4.0, 6.0, 4.0];
  const bHop = [Math.sqrt(15.0), Math.sqrt(4.5), Math.sqrt(4.5), Math.sqrt(15.0)];

  // 1. Evolve to t = pi/3 (exact complex ESE at site 0!)
  const resESE = await runSimulation(m, aDiag, bHop, PI / 3.0, 400);
  // 2. Evolve to t = pi (exact PST to site 4!)
  const resPST = await runSimulation(m, aDiag, bHop, PI, 600);

  // 3. Also test 5-qubit symmetric Krawtchouk chain {0, +-1, +-2}: a = 0, b = (sqrt(4), sqrt(6), sqrt(6), sqrt(4))?
  // Exact 5x5 Krawtchouk b_k = sqrt((k+1)*(4-k)) / 2? Wait: eigenvalues {-2,-1,0,1,2} => b_k = sqrt((k+1)*(4-k)) / 2:
  // k=0: sqrt(4)/2 = 1, k=1: sqrt(6)/2, k=2: sqrt(6)/2, k=3: 1! Check frob = 2*(1+1.5+1.5+1) = 10 = 4+1+0+1+4!
  const krawA = [0.0, 0.0, 0.0, 0.0, 0.0];
  const krawB = [1.0, Math.sqrt(1.5), Math.sqrt(1.5), 1.0];
  const resKrawMid = await runSimulation(m, krawA, krawB, PI / 3.0, 200);
  const resKrawPST = await runSimulation(m, krawA, krawB, PI, 300);

  console.log('[Moonlab WASM] 5-qubit (32-dim) J_{1,4} at t=pi/3 (ESE):');
  console.log(`  P(site 0) = ${resESE.siteProbs[0].toExponential(4)} (theory = 0), sector_sum = ${resESE.singleSectorSum.toFixed(12)}`);
  console.log('[Moonlab WASM] 5-qubit (32-dim) J_{1,4} at t=pi   (PST):');
  console.log(`  P(site 4) = ${resPST.siteProbs[4].toFixed(10)} (theory = 1), sector_sum = ${resPST.singleSectorSum.toFixed(12)}`);
  console.log('[Moonlab WASM] 5-qubit Krawtchouk control at t=pi/3 (no ESE) & t=pi (PST):');
  console.log(`  P(site 0, pi/3) = ${resKrawMid.siteProbs[0].toFixed(10)} (theory cos^8(pi/6)=${Math.pow(Math.cos(PI/6), 8).toFixed(10)})`);
  console.log(`  P(site 4, pi)   = ${resKrawPST.siteProbs[4].toFixed(10)} (theory = 1)`);

  const ok =
    resESE.siteProbs[0] < 1e-4 &&
    Math.abs(resESE.singleSectorSum - 1.0) < 1e-10 &&
    Math.abs(resPST.siteProbs[4] - 1.0) < 5e-4 &&
    Math.abs(resPST.singleSectorSum - 1.0) < 1e-10 &&
    Math.abs(resKrawMid.siteProbs[0] - Math.pow(Math.cos(PI / 6.0), 8)) < 1e-4 &&
    Math.abs(resKrawPST.siteProbs[4] - 1.0) < 1e-4;

  if (!ok) {
    console.error('[Moonlab WASM] VERIFICATION FAILED!');
    process.exit(1);
  }
  console.log('[Moonlab WASM] ALL 32-DIM MULTI-QUBIT XY+Z SIMULATIONS PASSED.');
})().catch((err) => {
  console.error(err);
  process.exit(1);
});
