# Frequently Asked Questions (FAQ)

### 1. Does this paper really prove Conjecture 4.1 of Escobar, Garcia, and Minenkova (`arXiv:2507.18767v1`)?
Yes. **Theorem 4** (`SpectralEclipse.conjecture_4_1_7x7` and `conjecture_4_1_7x7_unreduced`, isolated in `lean/Challenge.lean` as `target_theorem_4_conjecture_4_1` and `target_theorem_4_conjecture_4_1_unreduced`) proves both directions of Conjecture 4.1 without any `sorry` or custom axioms, both in reduced integer form ($\gcd(x,y,z)=1$) and for arbitrary positive real scaling $c>0$ and unreduced integers.

### 2. Why does the minimal-gap divisibility rule break at $N=8$ and $N=11$, yet survive at $N=9$?
By **Theorem 8** (`universal_phase_transition_3R_plus_2`), fusing an equidistant $R$-eigenvalue Krawtchouk core with an $r$-pair spectral cluster yields an asymptotic weight ratio $\Phi(R,r,M) \propto M^{r-R}$.
- Even chains have $R=2$ core $\{\pm 1/2\}$: $r=2$ ($N=6$) is critical ($\Phi = 1/2$), while $r=3$ ($N=8$) is supercritical ($\Phi \propto M \to \infty$), causing rupture for all $m \ge 1$ (**Theorem 5**).
- Odd chains have $R=3$ core $\{0, \pm 1\}$: $r=3$ ($N=9$) is critical ($\Phi = 1/4 \le 1/2$), and **Theorem 6** proves globally via second divided differences and 19 bivariate Bernstein certificates that $A_9(1,b,c,d;t) > 0$ on $[0,\pi)$ for *every* alternating-parity triple $1<b<c<d$. Rupture arrives at $r=4$ ($N=11$) with exact integer onset $M^* = 3\cdot 2^2 = 12$ ($m=6$, **Theorem 7**).

### 3. Why did Hypothesis H4 return a null result ($p_{\mathrm{Holm}}=0.9855$) in the QRNG disorder study?
Because complex-amplitude ESE in $J_{1,4}$ ($A(\pi/3)=0\in\mathbb{C}$) is a **codimension-2** zero in the complex plane, whereas real-amplitude ESE in symmetric chains (H1–H3) is a **codimension-1** transverse sign change on $\mathbb{R}$. Generic diagonal disorder $\varepsilon$ lifts a codimension-2 complex zero off the origin linearly as $O(\varepsilon)$, whereas a codimension-1 sign change is topologically protected by the Intermediate Value Theorem. Because `PREREGISTRATION.md` was locked in root commit `1dac632` before running any experiment (with the `v1.1.0` optimizer bug-fix documented transparently in [`DEVIATIONS.md`](../DEVIATIONS.md)), we report this genuine null honestly and transparently.

### 4. Why are there 8 different programming languages / quantum toolchains in `engines/`?
To eliminate single-implementation and single-paradigm blind spots (Build Standard B11/B12/B20): exact rational arithmetic over $\mathbb{Q}$ (Zig + SymPy Sturm) eliminates floating-point rounding; 32-dimensional 5-qubit gate simulation (Moonlab WASM) verifies the full many-body $XY+Z$ spin Hamiltonian without assuming single-excitation reduction; hardware AVX2+FMA assembly + C11 + C++20 verify numerical linear algebra and exposed the genuine B20 float64 cancellation hazard near $t=\pi$; Eshkol AD computes exact compiler-native derivatives; Safe Rust scans the $(R,r)$ phase diagram across $R=2\dots 5$; and vendored QGTL/QRNG directly verify the Fubini–Study metric and execute the pre-registered disorder trial.

### 5. Is this work peer-reviewed or submitted to arXiv / Palomar?
No. Version 1.1.0 is an **unrefereed research preprint** openly published on GitHub with full Lean 4.35.0 proofs, six-checker CI replay, and cryptographic timestamps. Independent human peer review and external operator replication (`B44`) remain open.
