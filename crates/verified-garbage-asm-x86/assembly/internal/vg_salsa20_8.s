// The functions of `src/internal/vg_salsa20_8.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_salsa20_8:
	mov eax, DWORD PTR [esp+4]
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [eax+16]
	movdqu xmm2, XMMWORD PTR [eax+32]
	movdqu xmm3, XMMWORD PTR [eax+48]
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	punpckldq xmm4, xmm1
	movdqa xmm5, xmm0
	punpckhdq xmm5, xmm1
	movdqa xmm6, xmm2
	punpckldq xmm6, xmm3
	movdqa xmm7, xmm2
	punpckhdq xmm7, xmm3
	movdqa xmm0, xmm4
	punpcklqdq xmm0, xmm6
	movdqa xmm1, xmm4
	punpckhqdq xmm1, xmm6
	movdqa xmm2, xmm5
	punpcklqdq xmm2, xmm7
	movdqa xmm3, xmm5
	punpckhqdq xmm3, xmm7
	pshufd xmm4, xmm3, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm1, 147
	movdqa xmm1, xmm4
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	pshufd xmm4, xmm1, 147
	pshufd xmm1, xmm3, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm3, xmm0
	punpckldq xmm3, xmm1
	movdqa xmm5, xmm0
	punpckhdq xmm5, xmm1
	movdqa xmm6, xmm2
	punpckldq xmm6, xmm4
	movdqa xmm7, xmm2
	punpckhdq xmm7, xmm4
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm6
	movdqa xmm1, xmm3
	punpckhqdq xmm1, xmm6
	movdqa xmm2, xmm5
	punpcklqdq xmm2, xmm7
	movdqa xmm4, xmm5
	punpckhqdq xmm4, xmm7
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm4, xmm4, 57
	movdqu xmm3, XMMWORD PTR [eax]
	movdqu xmm5, XMMWORD PTR [eax+16]
	movdqu xmm6, XMMWORD PTR [eax+32]
	movdqu xmm7, XMMWORD PTR [eax+48]
	paddd xmm0, xmm3
	paddd xmm1, xmm5
	paddd xmm2, xmm6
	paddd xmm4, xmm7
	movdqu XMMWORD PTR [eax], xmm0
	movdqu XMMWORD PTR [eax+16], xmm1
	movdqu XMMWORD PTR [eax+32], xmm2
	movdqu XMMWORD PTR [eax+48], xmm4
	ret
	.p2align 6
