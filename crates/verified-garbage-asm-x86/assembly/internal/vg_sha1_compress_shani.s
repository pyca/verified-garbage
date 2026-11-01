// The functions of `src/internal/vg_sha1_compress_shani.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress_shani:
	mov edx, DWORD PTR [esp+4]
	movdqu xmm0, XMMWORD PTR [edx]
	pshufd xmm0, xmm0, 27
	movdqu xmm1, XMMWORD PTR [edx+4]
	psrldq xmm1, 12
	pslldq xmm1, 12
	mov eax, 202182159
	movd xmm7, eax
	mov eax, 134810123
	movd xmm2, eax
	punpckldq xmm7, xmm2
	mov eax, 67438087
	movd xmm2, eax
	punpcklqdq xmm7, xmm2
	mov eax, 66051
	movd xmm2, eax
	pslldq xmm2, 12
	por xmm7, xmm2
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+12]
	test eax, eax
	je 20f
22:
	movdqu XMMWORD PTR [edx], xmm0
	movdqu XMMWORD PTR [edx+16], xmm1
	movdqu xmm3, XMMWORD PTR [ecx]
	pshufb xmm3, xmm7
	movdqa xmm2, xmm0
	paddd xmm1, xmm3
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ecx+16]
	pshufb xmm4, xmm7
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm4
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pshufb xmm5, xmm7
	movdqa xmm2, xmm0
	sha1nexte xmm1, xmm5
	sha1rnds4 xmm0, xmm1, 0
	movdqa xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ecx+48]
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
	movdqu xmm2, XMMWORD PTR [edx]
	paddd xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [edx+16]
	sha1nexte xmm1, xmm2
	add ecx, 64
	sub eax, 1
	jne 22b
	jmp 21f
20:
21:
	mov edx, DWORD PTR [esp+4]
	pshufd xmm0, xmm0, 27
	movdqa xmm2, xmm0
	psrldq xmm2, 4
	por xmm2, xmm1
	movdqu XMMWORD PTR [edx+4], xmm2
	movdqu XMMWORD PTR [edx], xmm0
	ret
	.p2align 6
