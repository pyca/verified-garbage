// The functions of `src/internal/vg_sha256_compress_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress_shani:
	lea rax, {VG_SHA256_SHANI_K}
	movdqu xmm8, XMMWORD PTR [rax+256]
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	pshufd xmm1, xmm1, 177
	pshufd xmm2, xmm2, 177
	movdqa xmm7, xmm2
	punpcklqdq xmm7, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm7
	test rdx, rdx
	je 20f
22:
	movdqa xmm9, xmm1
	movdqa xmm10, xmm2
	movdqu xmm3, XMMWORD PTR [rsi]
	pshufb xmm3, xmm8
	movdqu xmm0, XMMWORD PTR [rax]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm4, XMMWORD PTR [rsi+16]
	pshufb xmm4, xmm8
	movdqu xmm0, XMMWORD PTR [rax+16]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm5, XMMWORD PTR [rsi+32]
	pshufb xmm5, xmm8
	movdqu xmm0, XMMWORD PTR [rax+32]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [rsi+48]
	pshufb xmm6, xmm8
	movdqu xmm0, XMMWORD PTR [rax+48]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [rax+64]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqu xmm0, XMMWORD PTR [rax+80]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [rax+96]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [rax+112]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [rax+128]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqu xmm0, XMMWORD PTR [rax+144]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [rax+160]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [rax+176]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	movdqu xmm0, XMMWORD PTR [rax+192]
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	movdqu xmm0, XMMWORD PTR [rax+208]
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [rax+224]
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [rax+240]
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	paddd xmm1, xmm9
	paddd xmm2, xmm10
	add rsi, 64
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	movdqa xmm7, xmm1
	punpckhqdq xmm7, xmm2
	punpcklqdq xmm1, xmm2
	pshufd xmm7, xmm7, 177
	pshufd xmm1, xmm1, 177
	movdqu XMMWORD PTR [rdi], xmm7
	movdqu XMMWORD PTR [rdi+16], xmm1
	ret
	.p2align 6
