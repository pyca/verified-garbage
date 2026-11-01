// The functions of `src/internal/vg_aes_expand_key_scratch_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch_aesni:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	cmp ecx, 24
	je 20f
	cmp ecx, 32
	je 22f
	movdqu xmm1, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [edx], xmm1
	aeskeygenassist xmm3, xmm1, 1
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+16], xmm1
	aeskeygenassist xmm3, xmm1, 2
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+32], xmm1
	aeskeygenassist xmm3, xmm1, 4
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+48], xmm1
	aeskeygenassist xmm3, xmm1, 8
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+64], xmm1
	aeskeygenassist xmm3, xmm1, 16
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+80], xmm1
	aeskeygenassist xmm3, xmm1, 32
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+96], xmm1
	aeskeygenassist xmm3, xmm1, 64
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+112], xmm1
	aeskeygenassist xmm3, xmm1, 128
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+128], xmm1
	aeskeygenassist xmm3, xmm1, 27
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+144], xmm1
	aeskeygenassist xmm3, xmm1, 54
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+160], xmm1
	jmp 23f
22:
	movdqu xmm1, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+16]
	movdqu XMMWORD PTR [edx], xmm1
	movdqu XMMWORD PTR [edx+16], xmm2
	aeskeygenassist xmm3, xmm2, 1
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+32], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+48], xmm2
	aeskeygenassist xmm3, xmm2, 2
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+64], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+80], xmm2
	aeskeygenassist xmm3, xmm2, 4
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+96], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+112], xmm2
	aeskeygenassist xmm3, xmm2, 8
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+128], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+144], xmm2
	aeskeygenassist xmm3, xmm2, 16
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+160], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+176], xmm2
	aeskeygenassist xmm3, xmm2, 32
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+192], xmm1
	aeskeygenassist xmm3, xmm1, 0
	pshufd xmm3, xmm3, 170
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+208], xmm2
	aeskeygenassist xmm3, xmm2, 64
	pshufd xmm3, xmm3, 255
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+224], xmm1
23:
	jmp 21f
20:
	movdqu xmm1, XMMWORD PTR [eax]
	movdqu xmm2, XMMWORD PTR [eax+8]
	psrldq xmm2, 8
	movdqu XMMWORD PTR [edx], xmm1
	movdqu XMMWORD PTR [edx+16], xmm2
	aeskeygenassist xmm3, xmm2, 1
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+24], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+40], xmm2
	aeskeygenassist xmm3, xmm2, 2
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+48], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+64], xmm2
	aeskeygenassist xmm3, xmm2, 4
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+72], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+88], xmm2
	aeskeygenassist xmm3, xmm2, 8
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+96], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+112], xmm2
	aeskeygenassist xmm3, xmm2, 16
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+120], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+136], xmm2
	aeskeygenassist xmm3, xmm2, 32
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+144], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+160], xmm2
	aeskeygenassist xmm3, xmm2, 64
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+168], xmm1
	pshufd xmm3, xmm1, 255
	movdqa xmm4, xmm2
	pslldq xmm4, 4
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edx+184], xmm2
	aeskeygenassist xmm3, xmm2, 128
	pshufd xmm3, xmm3, 85
	movdqa xmm4, xmm1
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pslldq xmm4, 4
	pxor xmm1, xmm4
	pxor xmm1, xmm3
	movdqu XMMWORD PTR [edx+192], xmm1
21:
	ret
	.p2align 6
