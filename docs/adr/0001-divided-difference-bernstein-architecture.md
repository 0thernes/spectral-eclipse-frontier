# ADR-0001: Divided-Difference Reduction and Exact Rational Bernstein / SOS Certificates in Lean 4

- **Status:** Accepted
- **Date:** 2026-11-26
- **Author:** Alexander Stephen Donahue

## Context

Proving the Critical $9\times 9$ No-ESE Theorem (Theorem 6), Conjecture 4.1 for $7\times 7$ chains (Theorem 4), and the sharp $11\times 11$ threshold $m \ge 6 \iff M^* = 12$ (Theorem 7) requires establishing strict positivity of multivariate trigonometric sums and degree-8/degree-9 polynomials over semi-infinite domains without relying on floating-point interval arithmetic, external SMT solvers, or `native_decide` (which expands the trusted computing base).

## Decision

1. **Analytic Divided-Difference Reduction:** Express the mirror-symmetric Jacobi return amplitude $A(t)$ directly as a Newton divided difference of $\cos(\lambda t)$ (odd $N$) or $\sin(\lambda t)/\lambda$ (even $N$) over the distinct integer PST spectrum, reducing global non-vanishing on $(0, \pi)$ to exact cosine-polynomial sign bounds (`TrigBounds.lean`).
2. **Exact Rational Bivariate Bernstein Certificates (`Critical9x9Certs.lean`):** For Theorem 6 ($9\times 9$ critical chain with $\lambda_1 = 1$), partition the unbounded parameter cone into a compact core and asymptotic tail, certifying positivity via 19 explicit bivariate rational Bernstein expansions checked purely by kernel-verified `ring` / `norm_num` / `nlinarith` tactics — zero `native_decide`, zero external oracles.
3. **Exact Rational Sum-of-Squares Certificates (`RuptureAndPhase.lean`):** For Theorem 7 ($11\times 11$ threshold $m = 5$ vs. $m = 6$), certify global positivity of the subcritical degree-8 polynomial via 5 explicit rational sum-of-squares decompositions.

## Consequences

- **Positive:** Every single theorem (568 audited declarations) compiles strictly within `[propext, Classical.choice, Quot.sound]` and replays cleanly across all 6 independent Lean 4.35.0 proof checkers in `lake comparator --paranoid`.
- **Trade-off:** Constructing explicit rational certificates took substantial upfront algebraic factoring and sub-box splitting (e.g., splitting boxes `Z1, Z2, Z3a, Z5` in `Critical9x9.lean`), which is permanently preserved as fast, auditable kernel code.
