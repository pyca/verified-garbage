// The functions of `src/internal/vg_sha1_compress_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress_shani:
	movabs rax, 579005069656919567
	movq xmm7, rax
	movabs rax, 283686952306183
	movq xmm2, rax
	punpcklqdq xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [rdi]
	pshufd xmm0, xmm0, 27
	movdqu xmm1, XMMWORD PTR [rdi+4]
	psrldq xmm1, 12
	pslldq xmm1, 12
	test rdx, rdx
	je 20f
22:
	movdqa xmm8, xmm0
	movdqa xmm9, xmm1
	movdqu xmm3, XMMWORD PTR [rsi]
	pshufb xmm3, xmm7
	movdqa xmm2, xmm0
	paddd xmm1, xmm3
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [rsi+16]
	pshufb xmm4, xmm7
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm4
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	movdqu xmm5, XMMWORD PTR [rsi+32]
	pshufb xmm5, xmm7
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm5
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [rsi+48]
	pshufb xmm6, xmm7
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm6
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	sha1msg1 xmm3, xmm4
	pxor xmm3, xmm5
	sha1msg2 xmm3, xmm6
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm3
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	sha1msg1 xmm4, xmm5
	pxor xmm4, xmm6
	sha1msg2 xmm4, xmm3
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm4
	sha1rnds4 xmm0, xmm1, 1
	movdqa xmm1, xmm2
	sha1msg1 xmm5, xmm6
	pxor xmm5, xmm3
	sha1msg2 xmm5, xmm4
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm5
	sha1rnds4 xmm0, xmm1, 1
	movdqa xmm1, xmm2
	sha1msg1 xmm6, xmm3
	pxor xmm6, xmm4
	sha1msg2 xmm6, xmm5
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm6
	sha1rnds4 xmm0, xmm1, 1
	movdqa xmm1, xmm2
	sha1msg1 xmm3, xmm4
	pxor xmm3, xmm5
	sha1msg2 xmm3, xmm6
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm3
	sha1rnds4 xmm0, xmm1, 1
	movdqa xmm1, xmm2
	sha1msg1 xmm4, xmm5
	pxor xmm4, xmm6
	sha1msg2 xmm4, xmm3
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm4
	sha1rnds4 xmm0, xmm1, 1
	movdqa xmm1, xmm2
	sha1msg1 xmm5, xmm6
	pxor xmm5, xmm3
	sha1msg2 xmm5, xmm4
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm5
	sha1rnds4 xmm0, xmm1, 2
	movdqa xmm1, xmm2
	sha1msg1 xmm6, xmm3
	pxor xmm6, xmm4
	sha1msg2 xmm6, xmm5
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm6
	sha1rnds4 xmm0, xmm1, 2
	movdqa xmm1, xmm2
	sha1msg1 xmm3, xmm4
	pxor xmm3, xmm5
	sha1msg2 xmm3, xmm6
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm3
	sha1rnds4 xmm0, xmm1, 2
	movdqa xmm1, xmm2
	sha1msg1 xmm4, xmm5
	pxor xmm4, xmm6
	sha1msg2 xmm4, xmm3
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm4
	sha1rnds4 xmm0, xmm1, 2
	movdqa xmm1, xmm2
	sha1msg1 xmm5, xmm6
	pxor xmm5, xmm3
	sha1msg2 xmm5, xmm4
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm5
	sha1rnds4 xmm0, xmm1, 2
	movdqa xmm1, xmm2
	sha1msg1 xmm6, xmm3
	pxor xmm6, xmm4
	sha1msg2 xmm6, xmm5
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm6
	sha1rnds4 xmm0, xmm1, 3
	movdqa xmm1, xmm2
	sha1msg1 xmm3, xmm4
	pxor xmm3, xmm5
	sha1msg2 xmm3, xmm6
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm3
	sha1rnds4 xmm0, xmm1, 3
	movdqa xmm1, xmm2
	sha1msg1 xmm4, xmm5
	pxor xmm4, xmm6
	sha1msg2 xmm4, xmm3
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm4
	sha1rnds4 xmm0, xmm1, 3
	movdqa xmm1, xmm2
	sha1msg1 xmm5, xmm6
	pxor xmm5, xmm3
	sha1msg2 xmm5, xmm4
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm5
	sha1rnds4 xmm0, xmm1, 3
	movdqa xmm1, xmm2
	sha1msg1 xmm6, xmm3
	pxor xmm6, xmm4
	sha1msg2 xmm6, xmm5
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm6
	sha1rnds4 xmm0, xmm1, 3
	movdqa xmm1, xmm2
	paddd xmm0, xmm8
	sha1nexte xmm1, xmm9
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	pshufd xmm0, xmm0, 27
	movdqa xmm2, xmm0
	psrldq xmm2, 4
	por xmm2, xmm1
	movdqu XMMWORD PTR [rdi+4], xmm2
	movdqu XMMWORD PTR [rdi], xmm0
	ret
	.p2align 6
