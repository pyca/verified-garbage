// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 20f
	mov edx, DWORD PTR [esp+20]
	mov eax, 16711935
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	movdqu XMMWORD PTR [edx+208], xmm7
	mov eax, -520093696
	movd xmm2, eax
	mov eax, -2147483648
	movd xmm3, eax
	punpckldq xmm3, xmm2
	pxor xmm2, xmm2
	punpckldq xmm2, xmm3
	mov eax, DWORD PTR [esp+4]
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm0, xmm0, 27
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm1, xmm0
	psrld xmm1, 8
	pand xmm1, xmm7
	pand xmm0, xmm7
	pslld xmm0, 8
	por xmm0, xmm1
	movdqu XMMWORD PTR [edx], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+16], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+32], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+48], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+64], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+80], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+96], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx+112], xmm0
	movdqa xmm1, xmm0
	psllq xmm1, 63
	psraw xmm1, 15
	pshufd xmm1, xmm1, 78
	pand xmm1, xmm2
	psrlq xmm0, 1
	pxor xmm0, xmm1
	mov eax, DWORD PTR [esp+8]
	movdqu xmm3, XMMWORD PTR [eax]
	pshufd xmm3, xmm3, 27
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm1, xmm3
	psrld xmm1, 8
	pand xmm1, xmm7
	pand xmm3, xmm7
	pslld xmm3, 8
	por xmm3, xmm1
	mov eax, DWORD PTR [esp+12]
22:
	movdqu xmm4, XMMWORD PTR [eax]
	pshufd xmm4, xmm4, 27
	pshuflw xmm4, xmm4, 177
	pshufhw xmm4, xmm4, 177
	movdqa xmm5, xmm4
	psrld xmm5, 8
	pand xmm5, xmm7
	pand xmm4, xmm7
	pslld xmm4, 8
	por xmm4, xmm5
	pxor xmm4, xmm3
	movdqu XMMWORD PTR [edx+160], xmm4
	punpcklwd xmm4, xmm4
	movdqu xmm6, XMMWORD PTR [edx]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm0, xmm5, 255
	pand xmm0, xmm6
	pshufd xmm1, xmm5, 170
	pand xmm1, xmm6
	pshufd xmm2, xmm5, 85
	pand xmm2, xmm6
	pshufd xmm3, xmm5, 0
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+32]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+48]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+64]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+80]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+96]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+112]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqa xmm5, xmm3
	pslldq xmm5, 14
	psrldq xmm3, 2
	pxor xmm3, xmm2
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm1
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edx+128], xmm3
	movdqu XMMWORD PTR [edx+144], xmm5
	movdqu xmm6, XMMWORD PTR [edx]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm0, xmm5, 255
	pand xmm0, xmm6
	pshufd xmm1, xmm5, 170
	pand xmm1, xmm6
	pshufd xmm2, xmm5, 85
	pand xmm2, xmm6
	pshufd xmm3, xmm5, 0
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+32]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+48]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+64]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+80]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+96]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+112]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqa xmm5, xmm3
	pslldq xmm5, 14
	psrldq xmm3, 2
	pxor xmm3, xmm2
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm1
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm0
	movdqa xmm6, xmm3
	pslldq xmm6, 15
	psrldq xmm3, 1
	psrldq xmm5, 1
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edx+176], xmm3
	movdqu XMMWORD PTR [edx+192], xmm5
	movdqu xmm4, XMMWORD PTR [edx+160]
	punpckhwd xmm4, xmm4
	movdqu xmm6, XMMWORD PTR [edx]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm0, xmm5, 255
	pand xmm0, xmm6
	pshufd xmm1, xmm5, 170
	pand xmm1, xmm6
	pshufd xmm2, xmm5, 85
	pand xmm2, xmm6
	pshufd xmm3, xmm5, 0
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+32]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+48]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+64]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+80]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+96]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+112]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqa xmm5, xmm3
	pslldq xmm5, 14
	psrldq xmm3, 2
	pxor xmm3, xmm2
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm1
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edx+128], xmm3
	movdqu XMMWORD PTR [edx+144], xmm5
	movdqu xmm6, XMMWORD PTR [edx]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm0, xmm5, 255
	pand xmm0, xmm6
	pshufd xmm1, xmm5, 170
	pand xmm1, xmm6
	pshufd xmm2, xmm5, 85
	pand xmm2, xmm6
	pshufd xmm3, xmm5, 0
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+32]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+48]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+64]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+80]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+96]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [edx+112]
	movdqa xmm5, xmm4
	psraw xmm5, 15
	paddw xmm4, xmm4
	pshufd xmm7, xmm5, 255
	pand xmm7, xmm6
	pxor xmm0, xmm7
	pshufd xmm7, xmm5, 170
	pand xmm7, xmm6
	pxor xmm1, xmm7
	pshufd xmm7, xmm5, 85
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pshufd xmm7, xmm5, 0
	pand xmm7, xmm6
	pxor xmm3, xmm7
	movdqa xmm5, xmm3
	pslldq xmm5, 14
	psrldq xmm3, 2
	pxor xmm3, xmm2
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm1
	movdqa xmm6, xmm3
	pslldq xmm6, 14
	psrldq xmm5, 2
	pxor xmm5, xmm6
	psrldq xmm3, 2
	pxor xmm3, xmm0
	movdqa xmm6, xmm3
	pslldq xmm6, 15
	psrldq xmm3, 1
	psrldq xmm5, 1
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edx+144]
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	movdqu xmm7, XMMWORD PTR [edx+192]
	movdqa xmm0, xmm6
	pslldq xmm0, 8
	psrldq xmm6, 8
	psrldq xmm7, 8
	pxor xmm3, xmm6
	pxor xmm5, xmm0
	pxor xmm5, xmm7
	movdqa xmm6, xmm5
	psllq xmm6, 57
	movdqa xmm7, xmm6
	psllq xmm7, 5
	pxor xmm6, xmm7
	psllq xmm7, 1
	pxor xmm6, xmm7
	psrldq xmm6, 8
	pxor xmm3, xmm6
	pxor xmm3, xmm5
	psrlq xmm5, 1
	pxor xmm3, xmm5
	psrlq xmm5, 1
	pxor xmm3, xmm5
	psrlq xmm5, 5
	pxor xmm3, xmm5
	movdqu xmm7, XMMWORD PTR [edx+208]
	add eax, 16
	sub ecx, 1
	jne 22b
	pshufd xmm3, xmm3, 27
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm1, xmm3
	psrld xmm1, 8
	pand xmm1, xmm7
	pand xmm3, xmm7
	pslld xmm3, 8
	por xmm3, xmm1
	mov eax, DWORD PTR [esp+8]
	movdqu XMMWORD PTR [eax], xmm3
	jmp 21f
20:
21:
	ret
	.p2align 6
