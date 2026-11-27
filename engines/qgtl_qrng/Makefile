# SPDX-License-Identifier: Apache-2.0
CC      ?= gcc
CFLAGS  ?= -std=gnu11 -D_GNU_SOURCE -D_USE_MATH_DEFINES -O3 -Wall -Wextra -Wno-unused-parameter -Wno-unused-function -Wno-unused-variable -I../../third_party/qgtl/include -I../../third_party/qgtl/stub -I../../third_party/quantum_rng/src/quantum_rng -I../../third_party/quantum_rng/src/common -I../c -DSE_USE_AVX2_ASM=0
LDFLAGS ?= -lm

ifeq ($(OS),Windows_NT)
  EXE := .exe
else
  EXE :=
endif

SRCS = se_qgtl_qrng.c ../c/se_core.c ../../third_party/qgtl/src/quantum_geometric/distributed/differential_geometry.c ../../third_party/quantum_rng/src/quantum_rng/quantum_rng.c

.PHONY: all test clean

all: se_qgtl_qrng$(EXE)

se_qgtl_qrng$(EXE): $(SRCS)
	$(CC) $(CFLAGS) $(SRCS) -o $@ $(LDFLAGS)

test: se_qgtl_qrng$(EXE)
	mkdir -p ../../results
	./se_qgtl_qrng$(EXE) ../../results/qgtl_qrng_study.json

clean:
	rm -f se_qgtl_qrng se_qgtl_qrng.exe
