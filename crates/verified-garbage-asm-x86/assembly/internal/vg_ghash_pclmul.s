// The functions of `src/internal/vg_ghash_pclmul.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash_pclmul:
	mov eax, 66051
	movd xmm0, eax
	pslldq xmm0, 4
	mov eax, 67438087
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 134810123
	movd xmm5, eax
	por xmm0, xmm5
	pslldq xmm0, 4
	mov eax, 202182159
	movd xmm5, eax
	por xmm0, xmm5
	mov eax, -1040187392
	movd xmm1, eax
	pslldq xmm1, 4
	mov eax, 0
	movd xmm5, eax
	por xmm1, xmm5
	pslldq xmm1, 4
	mov eax, 0
	movd xmm5, eax
	por xmm1, xmm5
	pslldq xmm1, 4
	mov eax, 0
	movd xmm5, eax
	por xmm1, xmm5
	mov eax, DWORD PTR [esp+4]
	movdqu xmm7, XMMWORD PTR [eax]
	pshufb xmm7, xmm0
	mov eax, -1040187392
	movd xmm4, eax
	pslldq xmm4, 4
	mov eax, 0
	movd xmm5, eax
	por xmm4, xmm5
	pslldq xmm4, 4
	mov eax, 0
	movd xmm5, eax
	por xmm4, xmm5
	pslldq xmm4, 4
	mov eax, 1
	movd xmm5, eax
	por xmm4, xmm5
	mov eax, -1
	movd xmm5, eax
	punpckldq xmm5, xmm5
	punpcklqdq xmm5, xmm5
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm6, xmm7
	psrlq xmm6, 63
	pslldq xmm6, 8
	por xmm3, xmm6
	pshufd xmm6, xmm7, 255
	psrld xmm6, 31
	paddd xmm6, xmm5
	pandn xmm6, xmm4
	pxor xmm3, xmm6
	mov ecx, DWORD PTR [esp+8]
	movdqu xmm2, XMMWORD PTR [ecx]
	pshufb xmm2, xmm0
	mov edx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esp+16]
	test eax, eax
	je 20f
22:
	movdqu xmm7, XMMWORD PTR [edx]
	pshufb xmm7, xmm0
	pxor xmm2, xmm7
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	movdqa xmm7, xmm2
	pclmulqdq xmm7, xmm3, 0
	pxor xmm4, xmm7
	movdqa xmm7, xmm2
	pclmulqdq xmm7, xmm3, 17
	pxor xmm6, xmm7
	movdqa xmm7, xmm2
	pclmulqdq xmm7, xmm3, 1
	pxor xmm5, xmm7
	movdqa xmm7, xmm2
	pclmulqdq xmm7, xmm3, 16
	pxor xmm5, xmm7
	movdqa xmm7, xmm5
	psrldq xmm7, 8
	pxor xmm6, xmm7
	pslldq xmm5, 8
	pxor xmm4, xmm5
	movdqa xmm7, xmm4
	pclmulqdq xmm7, xmm1, 16
	pshufd xmm4, xmm4, 78
	pxor xmm4, xmm7
	movdqa xmm7, xmm4
	pclmulqdq xmm7, xmm1, 16
	pshufd xmm4, xmm4, 78
	pxor xmm4, xmm7
	movdqa xmm2, xmm6
	pxor xmm2, xmm4
	add edx, 16
	sub eax, 1
	jne 22b
	jmp 21f
20:
21:
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [ecx], xmm2
	ret
	.p2align 6
