// The functions of `src/internal/vg_blake2s_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_compress:
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+80], ebx
	mov DWORD PTR [eax+84], esi
	mov DWORD PTR [eax+88], edi
	mov esi, eax
	mov edi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esi+68], eax
	mov ecx, 0
	mov eax, DWORD PTR [esp+24]
	test eax, eax
	je 20f
	mov ecx, -1
	jmp 21f
20:
21:
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [esi+76], eax
	test eax, eax
	je 22f
24:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 1779033703
	mov DWORD PTR [esi+32], ecx
	mov ecx, -1150833019
	mov DWORD PTR [esi+36], ecx
	mov ecx, 1013904242
	mov DWORD PTR [esi+40], ecx
	mov ecx, -1521486534
	mov DWORD PTR [esi+44], ecx
	mov ecx, 1359893119
	xor ecx, DWORD PTR [esi+64]
	mov DWORD PTR [esi+48], ecx
	mov ecx, -1694144372
	xor ecx, DWORD PTR [esi+68]
	mov DWORD PTR [esi+52], ecx
	mov ecx, 528734635
	xor ecx, DWORD PTR [esi+72]
	mov DWORD PTR [esi+56], ecx
	mov ecx, 1541459225
	mov DWORD PTR [esi+60], ecx
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [eax+16]
	movdqu xmm2, XMMWORD PTR [esi+32]
	movdqu xmm3, XMMWORD PTR [esi+48]
	mov ecx, DWORD PTR [edi]
	mov edx, DWORD PTR [edi+8]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+24]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+12]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+28]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+56]
	mov edx, DWORD PTR [edi+32]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi+48]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+36]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+52]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+56]
	mov edx, DWORD PTR [edi+16]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+52]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi+32]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+24]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+4]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi]
	mov edx, DWORD PTR [edi+44]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+48]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+28]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+48]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+60]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+32]
	mov edx, DWORD PTR [edi]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+52]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+40]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+28]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+56]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+4]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+12]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+44]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+4]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+48]
	mov edx, DWORD PTR [edi+56]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+8]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+16]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+32]
	mov edx, DWORD PTR [edi+24]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+20]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+40]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi]
	mov edx, DWORD PTR [edi+28]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+60]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+56]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+24]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+4]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+48]
	mov edx, DWORD PTR [edi+32]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+24]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi]
	mov edx, DWORD PTR [edi+32]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+48]
	mov edx, DWORD PTR [edi+40]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+12]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+16]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+60]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+52]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+56]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+48]
	mov edx, DWORD PTR [edi+4]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+56]
	mov edx, DWORD PTR [edi+16]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+60]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+40]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+32]
	mov edx, DWORD PTR [edi]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+36]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+28]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+8]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+28]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+48]
	mov edx, DWORD PTR [edi+12]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+56]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+36]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+20]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+32]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+24]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+56]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+36]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+32]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi+48]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+4]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+8]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+16]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+40]
	mov edx, DWORD PTR [edi+32]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+4]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+16]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+24]
	mov edx, DWORD PTR [edi+20]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 147
	pshufd xmm2, xmm2, 57
	pshufd xmm3, xmm3, 78
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+60]
	movd xmm5, ecx
	movd xmm7, edx
	punpckldq xmm5, xmm7
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+12]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm5, xmm4
	mov ecx, DWORD PTR [edi]
	mov edx, DWORD PTR [edi+44]
	movd xmm6, ecx
	movd xmm7, edx
	punpckldq xmm6, xmm7
	mov ecx, DWORD PTR [edi+56]
	mov edx, DWORD PTR [edi+48]
	movd xmm4, ecx
	movd xmm7, edx
	punpckldq xmm4, xmm7
	punpcklqdq xmm6, xmm4
	paddd xmm0, xmm5
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 12
	pslld xmm4, 20
	por xmm1, xmm4
	paddd xmm0, xmm6
	paddd xmm0, xmm1
	pxor xmm3, xmm0
	movdqa xmm4, xmm3
	psrld xmm3, 8
	pslld xmm4, 24
	por xmm3, xmm4
	paddd xmm2, xmm3
	pxor xmm1, xmm2
	movdqa xmm4, xmm1
	psrld xmm1, 7
	pslld xmm4, 25
	por xmm1, xmm4
	pshufd xmm0, xmm0, 57
	pshufd xmm2, xmm2, 147
	pshufd xmm3, xmm3, 78
	pxor xmm0, xmm2
	pxor xmm1, xmm3
	movdqu xmm4, XMMWORD PTR [eax]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [eax], xmm0
	movdqu xmm4, XMMWORD PTR [eax+16]
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [eax+16], xmm1
	add edi, 64
	mov eax, DWORD PTR [esi+64]
	add eax, 64
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	adc eax, 0
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+76]
	sub eax, 1
	mov DWORD PTR [esi+76], eax
	jne 24b
	jmp 23f
22:
23:
	mov ebx, DWORD PTR [esi+80]
	mov edi, DWORD PTR [esi+88]
	mov esi, DWORD PTR [esi+84]
	ret
	.p2align 6
