// The functions of `src/internal/vg_aes_ctr32_aesni.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_aesni:
	movabs rax, 579005069656919567
	movq xmm10, rax
	movabs rax, 283686952306183
	movq xmm12, rax
	punpcklqdq xmm10, xmm12
	movabs rax, 1
	movq xmm11, rax
	movdqu xmm9, XMMWORD PTR [rdx]
	pshufb xmm9, xmm10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	cmp r8, 8
	jb 20f
22:
	movdqa xmm0, xmm9
	pshufb xmm0, xmm10
	paddd xmm9, xmm11
	movdqa xmm1, xmm9
	pshufb xmm1, xmm10
	paddd xmm9, xmm11
	movdqa xmm2, xmm9
	pshufb xmm2, xmm10
	paddd xmm9, xmm11
	movdqa xmm3, xmm9
	pshufb xmm3, xmm10
	paddd xmm9, xmm11
	movdqa xmm4, xmm9
	pshufb xmm4, xmm10
	paddd xmm9, xmm11
	movdqa xmm5, xmm9
	pshufb xmm5, xmm10
	paddd xmm9, xmm11
	movdqa xmm6, xmm9
	pshufb xmm6, xmm10
	paddd xmm9, xmm11
	movdqa xmm7, xmm9
	pshufb xmm7, xmm10
	paddd xmm9, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 23f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rcx]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [rcx], xmm0
	movdqu xmm8, XMMWORD PTR [rcx+16]
	pxor xmm1, xmm8
	movdqu XMMWORD PTR [rcx+16], xmm1
	movdqu xmm8, XMMWORD PTR [rcx+32]
	pxor xmm2, xmm8
	movdqu XMMWORD PTR [rcx+32], xmm2
	movdqu xmm8, XMMWORD PTR [rcx+48]
	pxor xmm3, xmm8
	movdqu XMMWORD PTR [rcx+48], xmm3
	movdqu xmm8, XMMWORD PTR [rcx+64]
	pxor xmm4, xmm8
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm8, XMMWORD PTR [rcx+80]
	pxor xmm5, xmm8
	movdqu XMMWORD PTR [rcx+80], xmm5
	movdqu xmm8, XMMWORD PTR [rcx+96]
	pxor xmm6, xmm8
	movdqu XMMWORD PTR [rcx+96], xmm6
	movdqu xmm8, XMMWORD PTR [rcx+112]
	pxor xmm7, xmm8
	movdqu XMMWORD PTR [rcx+112], xmm7
	add rcx, 128
	sub r8, 8
	cmp r8, 8
	jae 22b
	jmp 21f
20:
21:
	test r8, r8
	je 27f
29:
	movdqa xmm0, xmm9
	pshufb xmm0, xmm10
	paddd xmm9, xmm11
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 210f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 212f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 213f
212:
213:
	jmp 211f
210:
211:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rcx]
	pxor xmm0, xmm8
	movdqu XMMWORD PTR [rcx], xmm0
	add rcx, 16
	sub r8, 1
	jne 29b
	jmp 28f
27:
28:
	pshufb xmm9, xmm10
	movdqu XMMWORD PTR [rdx], xmm9
	ret
	.p2align 6
