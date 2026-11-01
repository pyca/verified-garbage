// The functions of `src/internal/vg_mlkem_cbd2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_cbd2:
	mov eax, 3329
	movq xmm15, rax
	pshufd xmm15, xmm15, 0
	mov eax, 16711935
	movq xmm8, rax
	pshufd xmm8, xmm8, 0
	mov eax, 5570645
	movq xmm9, rax
	pshufd xmm9, xmm9, 0
	mov eax, 3342387
	movq xmm10, rax
	pshufd xmm10, xmm10, 0
	mov eax, 2228258
	movq xmm11, rax
	pshufd xmm11, xmm11, 0
	mov eax, 983055
	movq xmm12, rax
	pshufd xmm12, xmm12, 0
	mov eax, 2
	movq xmm13, rax
	pshufd xmm13, xmm13, 0
	pxor xmm14, xmm14
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [rdi]
	movdqa xmm1, xmm0
	psrlw xmm1, 8
	pand xmm0, xmm8
	movdqa xmm2, xmm0
	psrlw xmm2, 1
	pand xmm2, xmm9
	pand xmm0, xmm9
	paddw xmm0, xmm2
	movdqa xmm2, xmm0
	psrlw xmm2, 2
	pand xmm2, xmm10
	pand xmm0, xmm10
	paddw xmm0, xmm11
	psubw xmm0, xmm2
	movdqa xmm2, xmm0
	psrlw xmm2, 4
	pand xmm0, xmm12
	movdqa xmm3, xmm1
	psrlw xmm3, 1
	pand xmm3, xmm9
	pand xmm1, xmm9
	paddw xmm1, xmm3
	movdqa xmm3, xmm1
	psrlw xmm3, 2
	pand xmm3, xmm10
	pand xmm1, xmm10
	paddw xmm1, xmm11
	psubw xmm1, xmm3
	movdqa xmm3, xmm1
	psrlw xmm3, 4
	pand xmm1, xmm12
	movdqa xmm4, xmm0
	punpcklwd xmm4, xmm2
	punpckhwd xmm0, xmm2
	movdqa xmm2, xmm1
	punpcklwd xmm2, xmm3
	punpckhwd xmm1, xmm3
	movdqa xmm5, xmm4
	punpcklwd xmm5, xmm14
	movdqa xmm6, xmm2
	punpcklwd xmm6, xmm14
	movdqa xmm7, xmm5
	punpcklqdq xmm7, xmm6
	punpckhqdq xmm5, xmm6
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi], xmm7
	psubd xmm5, xmm13
	movdqa xmm6, xmm5
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm5, xmm6
	movdqu XMMWORD PTR [rsi+16], xmm5
	punpckhwd xmm4, xmm14
	punpckhwd xmm2, xmm14
	movdqa xmm7, xmm4
	punpcklqdq xmm7, xmm2
	punpckhqdq xmm4, xmm2
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi+32], xmm7
	psubd xmm4, xmm13
	movdqa xmm6, xmm4
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm4, xmm6
	movdqu XMMWORD PTR [rsi+48], xmm4
	movdqa xmm5, xmm0
	punpcklwd xmm5, xmm14
	movdqa xmm6, xmm1
	punpcklwd xmm6, xmm14
	movdqa xmm7, xmm5
	punpcklqdq xmm7, xmm6
	punpckhqdq xmm5, xmm6
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi+64], xmm7
	psubd xmm5, xmm13
	movdqa xmm6, xmm5
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm5, xmm6
	movdqu XMMWORD PTR [rsi+80], xmm5
	punpckhwd xmm0, xmm14
	punpckhwd xmm1, xmm14
	movdqa xmm7, xmm0
	punpcklqdq xmm7, xmm1
	punpckhqdq xmm0, xmm1
	psubd xmm7, xmm13
	movdqa xmm6, xmm7
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm7, xmm6
	movdqu XMMWORD PTR [rsi+96], xmm7
	psubd xmm0, xmm13
	movdqa xmm6, xmm0
	psrad xmm6, 31
	pand xmm6, xmm15
	paddd xmm0, xmm6
	movdqu XMMWORD PTR [rsi+112], xmm0
	add rdi, 16
	add rsi, 128
	sub rcx, 1
	jne 20b
	ret
	.p2align 6
