// SPDX-FileCopyrightText: 2026 Alexander S. Donahue
// SPDX-License-Identifier: Apache-2.0
// Spectral Eclipse Frontier — Interactive Observatory Script (strict CSP script-src 'self')
"use strict";

const CHAINS = {
  "7_no":   { spec: [-3, -2, -1, 0, 1, 2, 3], complex: false, note: "No ESE (all t in [0, pi) strictly positive; A(t) = cos^6(t/2))" },
  "7_ese":  { spec: [-5, -4, -3, 0, 3, 4, 5], complex: false, note: "ESE at tau = 0.462184 (QSL bound pi/(2*sqrt(12.5)) = 0.444288, eta = 0.9613)" },
  "8_rup":  { spec: [-5.5, -4.5, -3.5, -0.5, 0.5, 3.5, 4.5, 5.5], complex: false, note: "Sharp even rupture N=8: ESE at tau = 0.632849 despite p_1 = 1" },
  "9_crit": { spec: [-22, -21, -20, -1, 0, 1, 20, 21, 22], complex: false, note: "Critical 9x9 No-ESE Theorem: strictly positive on all of [0, pi)" },
  "11_sub": { spec: [-13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13], complex: false, note: "11x11 subcritical m=5: SOS certified > 0 (interior min = 0.004194)" },
  "11_sup": { spec: [-15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15], complex: false, note: "11x11 supercritical m=6 (M*=12): ESE at tau = 0.198008 (4 interior roots)" },
  "j14":    { spec: [0, 1, 4, 9, 10], complex: true, note: "Staggered 5x5 J(1,4): exact complex ESE A(pi/3) = 0 in C, PST at pi (plot shows |A(t)|)" }
};

function computeWeights(spec) {
  const n = spec.length;
  const raw = [];
  let tot = 0;
  for (let k = 0; k < n; k++) {
    let p = 1;
    for (let j = 0; j < n; j++) {
      if (j !== k) p *= Math.abs(spec[k] - spec[j]);
    }
    raw.push(1 / p);
    tot += 1 / p;
  }
  return raw.map((v) => v / tot);
}

function drawChain(key) {
  const cfg = CHAINS[key];
  if (!cfg) return;
  const w = computeWeights(cfg.spec);
  const c = document.getElementById("plot");
  const ctx = c.getContext("2d");
  const W = c.width;
  const H = c.height;
  const padL = 56;
  const padR = 20;
  const padT = 20;
  const padB = 34;
  ctx.clearRect(0, 0, W, H);

  const N = 800;
  const ys = [];
  let minY = 1;
  let maxY = 1;
  for (let i = 0; i <= N; i++) {
    const t = (Math.PI * i) / N;
    let re = 0;
    let im = 0;
    for (let k = 0; k < cfg.spec.length; k++) {
      re += w[k] * Math.cos(cfg.spec[k] * t);
      im -= w[k] * Math.sin(cfg.spec[k] * t);
    }
    const y = cfg.complex ? Math.hypot(re, im) : re;
    ys.push(y);
    if (y < minY) minY = y;
    if (y > maxY) maxY = y;
  }
  minY = Math.min(minY - 0.08, -0.05);
  maxY = Math.max(maxY + 0.08, 1.05);
  const xMap = (i) => padL + (W - padL - padR) * (i / N);
  const yMap = (y) => padT + (H - padT - padB) * (1 - (y - minY) / (maxY - minY));

  ctx.strokeStyle = "#475569";
  ctx.setLineDash([5, 5]);
  ctx.lineWidth = 1;
  ctx.beginPath();
  ctx.moveTo(padL, yMap(0));
  ctx.lineTo(W - padR, yMap(0));
  ctx.stroke();
  ctx.setLineDash([]);

  ctx.strokeStyle = cfg.complex ? "#f97316" : "#38bdf8";
  ctx.lineWidth = 2.4;
  ctx.beginPath();
  for (let i = 0; i <= N; i++) {
    const x = xMap(i);
    const y = yMap(ys[i]);
    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }
  ctx.stroke();

  ctx.fillStyle = "#94a3b8";
  ctx.font = "12px ui-monospace, monospace";
  ctx.fillText("0", padL - 4, H - 10);
  ctx.fillText("pi/2", padL + (W - padL - padR) / 2 - 14, H - 10);
  ctx.fillText("pi", W - padR - 14, H - 10);
  ctx.fillText("1.0", 14, yMap(1.0) + 4);
  ctx.fillText("0.0", 14, yMap(0.0) + 4);
  document.getElementById("readout").textContent = cfg.note;
}

document.addEventListener("DOMContentLoaded", () => {
  const select = document.getElementById("chain-select");
  select.addEventListener("change", (e) => drawChain(e.target.value));
  drawChain(select.value || "7_ese");
});
