// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	mov QWORD PTR [r8+64], rbx
	mov QWORD PTR [r8+72], rbp
	mov QWORD PTR [r8+80], r12
	mov QWORD PTR [r8+88], r14
	mov QWORD PTR [r8+96], r15
	mov QWORD PTR [r8+104], r13
	mov r14, rsi
	mov rbx, rdi
	mov rbp, rdx
	mov r13, r8
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	add rsi, rsi
	mov r12, rdx
	add r12, rsi
	mov r15, rdi
	add r15, rsi
	add r15, rsi
	sub r15, 64
	movdqu xmm4, XMMWORD PTR [r15]
	movdqu xmm5, XMMWORD PTR [r15+16]
	movdqu xmm6, XMMWORD PTR [r15+32]
	movdqu xmm7, XMMWORD PTR [r15+48]
	pshufd xmm5, xmm5, 57
	pshufd xmm6, xmm6, 78
	pshufd xmm7, xmm7, 147
	movdqa xmm12, xmm4
	punpckldq xmm12, xmm5
	punpckhdq xmm4, xmm5
	movdqa xmm13, xmm6
	punpckldq xmm13, xmm7
	punpckhdq xmm6, xmm7
	movdqa xmm5, xmm12
	punpckhqdq xmm5, xmm13
	punpcklqdq xmm12, xmm13
	movdqa xmm7, xmm4
	punpckhqdq xmm7, xmm6
	punpcklqdq xmm4, xmm6
	pshufd xmm7, xmm7, 57
	pshufd xmm4, xmm4, 78
	pshufd xmm5, xmm5, 147
	movdqa xmm0, xmm12
	movdqa xmm1, xmm7
	movdqa xmm2, xmm4
	movdqa xmm3, xmm5
20:
	movdqu xmm4, XMMWORD PTR [rbx]
	movdqu xmm5, XMMWORD PTR [rbx+16]
	movdqu xmm6, XMMWORD PTR [rbx+32]
	movdqu xmm7, XMMWORD PTR [rbx+48]
	pshufd xmm5, xmm5, 57
	pshufd xmm6, xmm6, 78
	pshufd xmm7, xmm7, 147
	movdqa xmm12, xmm4
	punpckldq xmm12, xmm5
	punpckhdq xmm4, xmm5
	movdqa xmm13, xmm6
	punpckldq xmm13, xmm7
	punpckhdq xmm6, xmm7
	movdqa xmm5, xmm12
	punpckhqdq xmm5, xmm13
	punpcklqdq xmm12, xmm13
	movdqa xmm7, xmm4
	punpckhqdq xmm7, xmm6
	punpcklqdq xmm4, xmm6
	pshufd xmm7, xmm7, 57
	pshufd xmm4, xmm4, 78
	pshufd xmm5, xmm5, 147
	pxor xmm0, xmm12
	pxor xmm1, xmm7
	pxor xmm2, xmm4
	pxor xmm3, xmm5
	movdqa xmm8, xmm0
	movdqa xmm9, xmm1
	movdqa xmm10, xmm2
	movdqa xmm11, xmm3
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	paddd xmm0, xmm8
	paddd xmm1, xmm9
	paddd xmm2, xmm10
	paddd xmm3, xmm11
	movdqa xmm4, xmm0
	pshufd xmm5, xmm3, 57
	pshufd xmm6, xmm2, 78
	pshufd xmm7, xmm1, 147
	movdqa xmm12, xmm4
	punpckldq xmm12, xmm5
	punpckhdq xmm4, xmm5
	movdqa xmm13, xmm6
	punpckldq xmm13, xmm7
	punpckhdq xmm6, xmm7
	movdqa xmm5, xmm12
	punpckhqdq xmm5, xmm13
	punpcklqdq xmm12, xmm13
	movdqa xmm7, xmm4
	punpckhqdq xmm7, xmm6
	punpcklqdq xmm4, xmm6
	pshufd xmm5, xmm5, 147
	pshufd xmm4, xmm4, 78
	pshufd xmm7, xmm7, 57
	movdqu XMMWORD PTR [rbp], xmm12
	movdqu XMMWORD PTR [rbp+16], xmm5
	movdqu XMMWORD PTR [rbp+32], xmm4
	movdqu XMMWORD PTR [rbp+48], xmm7
	movdqu xmm4, XMMWORD PTR [rbx+64]
	movdqu xmm5, XMMWORD PTR [rbx+80]
	movdqu xmm6, XMMWORD PTR [rbx+96]
	movdqu xmm7, XMMWORD PTR [rbx+112]
	pshufd xmm5, xmm5, 57
	pshufd xmm6, xmm6, 78
	pshufd xmm7, xmm7, 147
	movdqa xmm12, xmm4
	punpckldq xmm12, xmm5
	punpckhdq xmm4, xmm5
	movdqa xmm13, xmm6
	punpckldq xmm13, xmm7
	punpckhdq xmm6, xmm7
	movdqa xmm5, xmm12
	punpckhqdq xmm5, xmm13
	punpcklqdq xmm12, xmm13
	movdqa xmm7, xmm4
	punpckhqdq xmm7, xmm6
	punpcklqdq xmm4, xmm6
	pshufd xmm7, xmm7, 57
	pshufd xmm4, xmm4, 78
	pshufd xmm5, xmm5, 147
	pxor xmm0, xmm12
	pxor xmm1, xmm7
	pxor xmm2, xmm4
	pxor xmm3, xmm5
	movdqa xmm8, xmm0
	movdqa xmm9, xmm1
	movdqa xmm10, xmm2
	movdqa xmm11, xmm3
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 57
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	movdqa xmm4, xmm1
	movdqa xmm5, xmm1
	paddd xmm4, xmm0
	paddd xmm5, xmm0
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	movdqa xmm5, xmm0
	paddd xmm4, xmm3
	paddd xmm5, xmm3
	pslld xmm4, 9
	psrld xmm5, 23
	por xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm4, xmm3
	movdqa xmm5, xmm3
	paddd xmm4, xmm2
	paddd xmm5, xmm2
	pslld xmm4, 13
	psrld xmm5, 19
	por xmm4, xmm5
	pxor xmm1, xmm4
	movdqa xmm4, xmm2
	movdqa xmm5, xmm2
	paddd xmm4, xmm1
	paddd xmm5, xmm1
	pslld xmm4, 18
	psrld xmm5, 14
	por xmm4, xmm5
	pxor xmm0, xmm4
	pshufd xmm3, xmm3, 147
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	paddd xmm0, xmm8
	paddd xmm1, xmm9
	paddd xmm2, xmm10
	paddd xmm3, xmm11
	movdqa xmm4, xmm0
	pshufd xmm5, xmm3, 57
	pshufd xmm6, xmm2, 78
	pshufd xmm7, xmm1, 147
	movdqa xmm12, xmm4
	punpckldq xmm12, xmm5
	punpckhdq xmm4, xmm5
	movdqa xmm13, xmm6
	punpckldq xmm13, xmm7
	punpckhdq xmm6, xmm7
	movdqa xmm5, xmm12
	punpckhqdq xmm5, xmm13
	punpcklqdq xmm12, xmm13
	movdqa xmm7, xmm4
	punpckhqdq xmm7, xmm6
	punpcklqdq xmm4, xmm6
	pshufd xmm5, xmm5, 147
	pshufd xmm4, xmm4, 78
	pshufd xmm7, xmm7, 57
	movdqu XMMWORD PTR [r12], xmm12
	movdqu XMMWORD PTR [r12+16], xmm5
	movdqu XMMWORD PTR [r12+32], xmm4
	movdqu XMMWORD PTR [r12+48], xmm7
	mov r15, r12
	add rbx, 128
	add rbp, 64
	add r12, 64
	sub r14, 1
	jne 20b
	mov rbx, QWORD PTR [r13+64]
	mov rbp, QWORD PTR [r13+72]
	mov r12, QWORD PTR [r13+80]
	mov r14, QWORD PTR [r13+88]
	mov r15, QWORD PTR [r13+96]
	mov r13, QWORD PTR [r13+104]
	ret
	.p2align 6
