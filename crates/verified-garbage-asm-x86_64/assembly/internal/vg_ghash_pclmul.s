// The functions of `src/internal/vg_ghash_pclmul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash_pclmul:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [rdi]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	movdqu xmm2, XMMWORD PTR [rsi]
	pshufb xmm2, xmm0
	cmp rcx, 4
	jb 20f
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	jmp 21f
20:
21:
	cmp rcx, 4
	jb 22f
24:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [rdx]
	pshufb xmm7, xmm0
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [rdx+16]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm5, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [rdx+32]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm4, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [rdx+48]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add rdx, 64
	sub rcx, 4
	cmp rcx, 4
	jae 24b
	jmp 23f
22:
23:
	test rcx, rcx
	je 25f
27:
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqu xmm7, XMMWORD PTR [rdx]
	pshufb xmm7, xmm0
	pxor xmm7, xmm2
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	add rdx, 16
	sub rcx, 1
	jne 27b
	jmp 26f
25:
26:
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [rsi], xmm2
	ret
	.p2align 6
