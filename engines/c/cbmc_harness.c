/* SPDX-FileCopyrightText: 2026 Alexander S. Donahue
 * SPDX-License-Identifier: Apache-2.0
 *
 * Bounded Model Checking harness (Build Standard B25, CBMC) verifying
 * memory-safety, loop-bound termination, and division-by-zero freedom of the
 * core Jacobi SpMV routine in se_core.c.
 *
 * Run with CBMC:
 *   cbmc --bounds-check --pointer-check --div-by-zero-check \
 *        --unwind 12 -DSE_USE_AVX2_ASM=0 cbmc_harness.c se_core.c
 */
#include <stddef.h>
#include "se_core.h"

#ifdef CBMC
extern int nondet_int(void);
extern double nondet_double(void);
extern void __CPROVER_assume(int);
extern void __CPROVER_assert(int, const char *);
#else
static int nondet_int(void) { return 5; }
static double nondet_double(void) { return 1.0; }
static void __CPROVER_assume(int cond) { (void)cond; }
static void __CPROVER_assert(int cond, const char *msg) { (void)cond; (void)msg; }
#endif

int main(void) {
    int n_raw = nondet_int();
    __CPROVER_assume(n_raw >= 2 && n_raw <= 8);
    size_t n = (size_t)n_raw;

    double a[8];
    double b[8];
    double x[8];
    double y[8];

    for (size_t i = 0; i < n; ++i) {
        a[i] = nondet_double();
        x[i] = nondet_double();
        y[i] = 0.0;
        __CPROVER_assume(a[i] >= -10.0 && a[i] <= 10.0);
        __CPROVER_assume(x[i] >= -1.0 && x[i] <= 1.0);
        if (i + 1 < n) {
            b[i] = nondet_double();
            __CPROVER_assume(b[i] > 0.0 && b[i] <= 10.0);
        }
    }

    se_spmv_ctx ctx = {n, a, b, x, y};
    se_jacobi_spmv_scalar(&ctx);

    __CPROVER_assert(y[0] >= -20.0 && y[0] <= 20.0, "y[0] bounded by |a[0]| + |b[0]|");
    return 0;
}
