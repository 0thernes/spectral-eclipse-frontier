/* SPDX-FileCopyrightText: 2026 Alexander S. Donahue
 * SPDX-License-Identifier: Apache-2.0
 *
 * Coverage-guided libFuzzer harness (Build Standard B15) for ISO C11
 * Hochstadt persymmetric Jacobi reconstruction and return-amplitude
 * evaluation (se_core.c).
 *
 * Build & run on Linux with Clang:
 *   clang -std=c11 -O1 -g -fsanitize=fuzzer,address,undefined \
 *         -DSE_USE_AVX2_ASM=0 fuzz_hochstadt.c se_core.c -lm -o fuzz_hochstadt
 *   ./fuzz_hochstadt -max_total_time=10
 */
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "se_core.h"

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 4) {
        return 0;
    }

    /* Map first byte to valid chain length N in [4, 15] */
    size_t n = 4 + (size_t)(data[0] % 12);
    size_t half = n / 2;
    if (size < 2 + half) {
        return 0;
    }

    double spec[16];
    double a[16];
    double b[16];
    double w[16];

    double acc = (n % 2 == 0) ? 1.0 : 0.0;
    if (n % 2 == 1) {
        spec[half] = 0.0;
    }
    for (size_t k = 0; k < half; ++k) {
        double gap = 1.0 + (double)(data[1 + k] % 7);
        acc += gap;
        if (n % 2 == 0) {
            spec[half + k] = acc;
            spec[half - 1 - k] = -acc;
        } else {
            spec[half + 1 + k] = acc;
            spec[half - 1 - k] = -acc;
        }
    }

    if (se_reconstruct_persymmetric_jacobi(n, spec, a, b, w) != 0) {
        return 0;
    }

    for (size_t i = 0; i < n; ++i) {
        if (!isfinite(a[i]) || !isfinite(w[i]) || w[i] <= 0.0) {
            abort();
        }
    }
    for (size_t i = 0; i + 1 < n; ++i) {
        if (!isfinite(b[i]) || b[i] <= 0.0) {
            abort();
        }
        double sym_err = fabs(b[i] - b[n - 2 - i]);
        if (sym_err > 1e-6 * (1.0 + b[i])) {
            abort();
        }
    }

    double t = 0.01 + 3.12 * ((double)data[size - 1] / 255.0);
    double re = 0.0;
    double im = 0.0;
    se_return_amplitude_complex(n, spec, w, t, &re, &im);
    double mag = hypot(re, im);
    if (!isfinite(mag) || mag > 1.0 + 1e-6) {
        abort();
    }
    return 0;
}
