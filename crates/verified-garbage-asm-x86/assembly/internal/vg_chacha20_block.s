// The functions of `src/internal/vg_chacha20_block.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_block:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [eax]
	movd xmm0, edx
	mov edx, DWORD PTR [eax+4]
	movd xmm4, edx
	punpckldq xmm0, xmm4
	mov edx, DWORD PTR [eax+8]
	movd xmm4, edx
	mov edx, DWORD PTR [eax+12]
	movd xmm5, edx
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	mov edx, DWORD PTR [eax+16]
	movd xmm1, edx
	mov edx, DWORD PTR [eax+20]
	movd xmm4, edx
	punpckldq xmm1, xmm4
	mov edx, DWORD PTR [eax+24]
	movd xmm4, edx
	mov edx, DWORD PTR [eax+28]
	movd xmm5, edx
	punpckldq xmm4, xmm5
	punpcklqdq xmm1, xmm4
	mov edx, DWORD PTR [eax+32]
	movd xmm2, edx
	mov edx, DWORD PTR [eax+36]
	movd xmm4, edx
	punpckldq xmm2, xmm4
	mov edx, DWORD PTR [eax+40]
	movd xmm4, edx
	mov edx, DWORD PTR [eax+44]
	movd xmm5, edx
	punpckldq xmm4, xmm5
	punpcklqdq xmm2, xmm4
	mov edx, DWORD PTR [eax+48]
	movd xmm3, edx
	mov edx, DWORD PTR [eax+52]
	movd xmm4, edx
	punpckldq xmm3, xmm4
	mov edx, DWORD PTR [eax+56]
	movd xmm4, edx
	mov edx, DWORD PTR [eax+60]
	movd xmm5, edx
	punpckldq xmm4, xmm5
	punpcklqdq xmm3, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 12
	psrld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	pslld xmm3, 8
	psrld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	pslld xmm1, 7
	psrld xmm4, 25
	por xmm1, xmm4
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqu xmm4, XMMWORD PTR [eax]
	paddd xmm0, xmm4
	movdqu XMMWORD PTR [ecx], xmm0
	movdqu xmm4, XMMWORD PTR [eax+16]
	paddd xmm1, xmm4
	movdqu XMMWORD PTR [ecx+16], xmm1
	movdqu xmm4, XMMWORD PTR [eax+32]
	paddd xmm2, xmm4
	movdqu XMMWORD PTR [ecx+32], xmm2
	movdqu xmm4, XMMWORD PTR [eax+48]
	paddd xmm3, xmm4
	movdqu XMMWORD PTR [ecx+48], xmm3
	ret
	.p2align 6
