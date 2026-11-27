# SPDX-License-Identifier: Apache-2.0
# Portable Makefile for ISO C11 + NASM x86-64 AVX2+FMA engine (Linux, macOS, Windows/MinGW)

CC      ?= gcc
NASM    ?= nasm
CFLAGS  ?= -std=c11 -O3 -Wall -Wextra -Werror -Wpedantic -Wshadow -Wconversion -Wno-sign-conversion
LDFLAGS ?= -lm

UNAME_S := $(shell uname -s 2>/dev/null || echo Windows)
UNAME_M := $(shell uname -m 2>/dev/null || echo x86_64)

ifeq ($(OS),Windows_NT)
  EXE      := .exe
  ASM_FMT  := win64
  ASM_DEF  := -DWIN64
  USE_ASM  ?= 1
else ifeq ($(UNAME_S),Linux)
  EXE      :=
  ifeq ($(UNAME_M),x86_64)
    ASM_FMT := elf64
    ASM_DEF :=
    USE_ASM ?= 1
  else
    USE_ASM ?= 0
  endif
else
  EXE      :=
  USE_ASM  ?= 0
endif

ifeq ($(USE_ASM),1)
  ASM_OBJ  := jacobi_avx2.o
  ASM_FLAG := -DSE_USE_AVX2_ASM=1
else
  ASM_OBJ  :=
  ASM_FLAG := -DSE_USE_AVX2_ASM=0
endif

.PHONY: all test asan fuzz cbmc clean

all: test_c_core$(EXE)

jacobi_avx2.o: ../asm/jacobi_avx2.asm
	$(NASM) -f $(ASM_FMT) $(ASM_DEF) $< -o $@

test_c_core$(EXE): se_core.c se_core.h test_c_core.c $(ASM_OBJ)
	$(CC) $(CFLAGS) $(ASM_FLAG) se_core.c test_c_core.c $(ASM_OBJ) -o $@ $(LDFLAGS)

test: test_c_core$(EXE)
	./test_c_core$(EXE)

asan: se_core.c se_core.h test_c_core.c $(ASM_OBJ)
	$(CC) -std=c11 -O1 -g -Wall -Wextra -Werror -fsanitize=address,undefined -fno-omit-frame-pointer $(ASM_FLAG) se_core.c test_c_core.c $(ASM_OBJ) -o test_c_core_asan$(EXE) $(LDFLAGS)
	./test_c_core_asan$(EXE)

fuzz: fuzz_hochstadt.c se_core.c se_core.h
	clang -std=c11 -O1 -g -Wall -Wextra -Werror -fsanitize=fuzzer,address,undefined -DSE_USE_AVX2_ASM=0 fuzz_hochstadt.c se_core.c -lm -o fuzz_hochstadt$(EXE)
	./fuzz_hochstadt$(EXE) -max_total_time=5

cbmc: cbmc_harness.c se_core.c se_core.h
	cbmc --bounds-check --pointer-check --div-by-zero-check --unwind 12 -DSE_USE_AVX2_ASM=0 cbmc_harness.c se_core.c

clean:
	rm -f jacobi_avx2.o test_c_core test_c_core.exe test_c_core_asan test_c_core_asan.exe fuzz_hochstadt fuzz_hochstadt.exe
