// The functions of `src/internal/vg_aes_expand_key_scratch_aesni.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch_aesni:
	pcmpeqd xmm5, xmm5
	psrld xmm5, 31
	movdqa xmm6, xmm5
	paddd xmm6, xmm6
	movdqa xmm7, xmm6
	paddd xmm7, xmm7
	movdqa xmm8, xmm7
	paddd xmm8, xmm8
	movdqa xmm9, xmm8
	paddd xmm9, xmm9
	movdqa xmm10, xmm9
	paddd xmm10, xmm10
	movdqa xmm11, xmm10
	paddd xmm11, xmm11
	movdqa xmm12, xmm11
	paddd xmm12, xmm12
	cmp rsi, 24
	je 20f
	cmp rsi, 32
	je 22f
	movdqa xmm13, xmm5
	pxor xmm13, xmm6
	pxor xmm13, xmm8
	pxor xmm13, xmm9
	movdqa xmm14, xmm13
	paddd xmm14, xmm14
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu XMMWORD PTR [rdx], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+16], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm13
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	pshufd xmm3, xmm1, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm14
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	jmp 23f
22:
	pxor xmm15, xmm15
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+16]
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+32], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+80], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+128], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+176], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
	pshufd xmm3, xmm1, 255
	aesenclast xmm3, xmm15
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	pslldq xmm4, 8
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+208], xmm2
	pshufd xmm3, xmm2, 255
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+224], xmm1
23:
	jmp 21f
20:
	movdqu xmm1, XMMWORD PTR [rdi]
	movdqu xmm2, XMMWORD PTR [rdi+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [rdx], xmm1
	movdqu XMMWORD PTR [rdx+16], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm5
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+24], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+40], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm6
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+48], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+64], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm7
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+72], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+88], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm8
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+96], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+112], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm9
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+120], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+136], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm10
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+144], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+160], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm11
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+168], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [rdx+184], xmm2
	pshufd xmm3, xmm2, 85
	psrldq xmm3, 1
	pshufd xmm3, xmm3, 0
	aesenclast xmm3, xmm12
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm1
	pslldq xmm4, 8
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [rdx+192], xmm1
21:
	ret
	.p2align 6
