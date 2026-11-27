# SPDX-License-Identifier: Apache-2.0
CXX      ?= g++
CXXFLAGS ?= -std=c++20 -O3 -Wall -Wextra -Werror -Wpedantic -Wshadow

ifeq ($(OS),Windows_NT)
  EXE := .exe
else
  EXE :=
endif

.PHONY: all test clean

all: se_propagator$(EXE)

se_propagator$(EXE): se_propagator.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

test: se_propagator$(EXE)
	./se_propagator$(EXE)

clean:
	rm -f se_propagator se_propagator.exe
