; SPDX-License-Identifier: Apache-2.0
; Copyright (c) 2026 Alexander Stephen Donahue
;
; Spectral Eclipse Frontier -- Dual-ABI (Win64 / System V AMD64) x86-64 AVX2+FMA
; Kernels for Persymmetric Tridiagonal Jacobi Operators & Chebyshev Propagation.
;
; Assemble on Windows (x64): nasm -f win64 -DWIN64 jacobi_avx2.asm -o jacobi_avx2.obj
; Assemble on Linux   (x64): nasm -f elf64 jacobi_avx2.asm -o jacobi_avx2.o

default rel
section .rodata
align 32
const_two_pd:
    dq 2.0, 2.0, 2.0, 2.0

section .text

; ---------------------------------------------------------------------------
; struct se_spmv_ctx {
;     size_t n;           // offset 0
;     const double *a;    // offset 8   (diagonal, length n)
;     const double *b;    // offset 16  (off-diagonal, length n-1)
;     const double *x;    // offset 24  (input vector, length n)
;     double *y;          // offset 32  (output vector, length n)
; };
; void se_jacobi_spmv_avx2(const se_spmv_ctx *ctx);
;
; Computes y = J * x for an n x n real symmetric tridiagonal Jacobi matrix:
;   y[0]   = a[0]*x[0] + b[0]*x[1]
;   y[i]   = b[i-1]*x[i-1] + a[i]*x[i] + b[i]*x[i+1]   (1 <= i <= n-2)
;   y[n-1] = b[n-2]*x[n-2] + a[n-1]*x[n-1]
; Uses only volatile XMM/YMM registers (ymm0..ymm5) so Win64 xmm6..xmm15 are untouched.
; ---------------------------------------------------------------------------
global se_jacobi_spmv_avx2
se_jacobi_spmv_avx2:
    push rbx
    push r12
    push r13
    push r14
    push r15

%ifdef WIN64
    mov rax, rcx            ; ctx pointer
%else
    mov rax, rdi            ; ctx pointer
%endif

    mov r10, [rax + 0]      ; n
    test r10, r10
    jz .done

    mov r11, [rax + 8]      ; a
    mov r12, [rax + 16]     ; b
    mov r13, [rax + 24]     ; x
    mov r14, [rax + 32]     ; y

    cmp r10, 1
    jne .n_ge_2
    ; n == 1: y[0] = a[0] * x[0]
    vmovsd xmm0, [r11]
    vmulsd xmm0, xmm0, [r13]
    vmovsd [r14], xmm0
    jmp .done

.n_ge_2:
    ; Boundary i = 0: y[0] = a[0]*x[0] + b[0]*x[1]
    vmovsd xmm0, [r11]
    vmulsd xmm0, xmm0, [r13]
    vmovsd xmm1, [r12]
    vfmadd231sd xmm0, xmm1, [r13 + 8]
    vmovsd [r14], xmm0

    ; Interior loop: i = 1 .. n - 2
    mov rbx, 1              ; i = 1
    mov r15, r10
    dec r15                 ; limit = n - 1

    ; AVX2 4-wide loop while i + 4 <= n - 1
    mov rcx, r15
    sub rcx, 4              ; last valid vector start = n - 5
    cmp rbx, rcx
    jg .scalar_interior

.avx2_loop:
    ; offset = i * 8
    lea rdx, [rbx * 8]
    ; ymm0 = a[i..i+3] * x[i..i+3]
    vmovupd ymm0, [r11 + rdx]
    vmovupd ymm1, [r13 + rdx]
    vmulpd ymm0, ymm0, ymm1
    ; ymm0 += b[i-1..i+2] * x[i-1..i+2]
    vmovupd ymm2, [r12 + rdx - 8]
    vmovupd ymm3, [r13 + rdx - 8]
    vfmadd231pd ymm0, ymm2, ymm3
    ; ymm0 += b[i..i+3] * x[i+1..i+4]
    vmovupd ymm4, [r12 + rdx]
    vmovupd ymm5, [r13 + rdx + 8]
    vfmadd231pd ymm0, ymm4, ymm5
    ; store y[i..i+3]
    vmovupd [r14 + rdx], ymm0

    add rbx, 4
    cmp rbx, rcx
    jle .avx2_loop

.scalar_interior:
    cmp rbx, r15
    jge .last_elem

.scalar_loop:
    lea rdx, [rbx * 8]
    vmovsd xmm0, [r11 + rdx]
    vmulsd xmm0, xmm0, [r13 + rdx]
    vmovsd xmm1, [r12 + rdx - 8]
    vfmadd231sd xmm0, xmm1, [r13 + rdx - 8]
    vmovsd xmm2, [r12 + rdx]
    vfmadd231sd xmm0, xmm2, [r13 + rdx + 8]
    vmovsd [r14 + rdx], xmm0
    inc rbx
    cmp rbx, r15
    jl .scalar_loop

.last_elem:
    ; Boundary i = n - 1: y[n-1] = b[n-2]*x[n-2] + a[n-1]*x[n-1]
    lea rdx, [r15 * 8]
    vmovsd xmm0, [r11 + rdx]
    vmulsd xmm0, xmm0, [r13 + rdx]
    vmovsd xmm1, [r12 + rdx - 8]
    vfmadd231sd xmm0, xmm1, [r13 + rdx - 8]
    vmovsd [r14 + rdx], xmm0

.done:
    vzeroupper
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbx
    ret

; ---------------------------------------------------------------------------
; void se_cheb_combine_avx2(size_t n, const double *jx,
;                           const double *t_prev, double *t_next);
;
; Computes Chebyshev recurrence vector update:
;   t_next[i] = 2.0 * jx[i] - t_prev[i]   for 0 <= i < n.
; ---------------------------------------------------------------------------
global se_cheb_combine_avx2
se_cheb_combine_avx2:
%ifdef WIN64
    ; rcx = n, rdx = jx, r8 = t_prev, r9 = t_next
    mov r10, rcx
    mov r11, rdx
    mov rax, r8
    mov rdx, r9
%else
    ; rdi = n, rsi = jx, rdx = t_prev, rcx = t_next
    mov r10, rdi
    mov r11, rsi
    mov rax, rdx
    mov rdx, rcx
%endif

    xor r8, r8              ; i = 0
    vmovapd ymm2, [const_two_pd]

    mov r9, r10
    and r9, ~3              ; floor(n / 4) * 4
    cmp r8, r9
    jge .cheb_tail

.cheb_vec_loop:
    lea rcx, [r8 * 8]
    vmovupd ymm0, [r11 + rcx]
    vmovupd ymm1, [rax + rcx]
    vfmsub213pd ymm0, ymm2, ymm1    ; ymm0 = 2.0 * jx - t_prev
    vmovupd [rdx + rcx], ymm0
    add r8, 4
    cmp r8, r9
    jl .cheb_vec_loop

.cheb_tail:
    cmp r8, r10
    jge .cheb_done

.cheb_scalar_loop:
    lea rcx, [r8 * 8]
    vmovsd xmm0, [r11 + rcx]
    vmovsd xmm1, [rax + rcx]
    vfmsub213sd xmm0, xmm2, xmm1
    vmovsd [rdx + rcx], xmm0
    inc r8
    cmp r8, r10
    jl .cheb_scalar_loop

.cheb_done:
    vzeroupper
    ret

%ifidn __OUTPUT_FORMAT__, elf64
section .note.GNU-stack noalloc noexec nowrite progbits
%endif
