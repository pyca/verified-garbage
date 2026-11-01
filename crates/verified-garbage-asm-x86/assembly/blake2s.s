// The functions of `src/blake2s.rs` of `verified-garbage-asm-x86`, as text: generated from
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

vg_blake2s_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 20f
	mov edx, 0
	mov DWORD PTR [eax+32], edx
	mov DWORD PTR [eax+36], edx
	mov DWORD PTR [eax+40], edx
	mov DWORD PTR [eax+44], edx
	mov DWORD PTR [eax+48], edx
	mov DWORD PTR [eax+52], edx
	mov DWORD PTR [eax+56], edx
	mov DWORD PTR [eax+60], edx
	mov DWORD PTR [eax+64], edx
	mov DWORD PTR [eax+68], edx
	mov DWORD PTR [eax+72], edx
	mov DWORD PTR [eax+76], edx
	mov DWORD PTR [eax+80], edx
	mov DWORD PTR [eax+84], edx
	mov DWORD PTR [eax+88], edx
	mov DWORD PTR [eax+92], edx
	mov DWORD PTR [eax], ebx
	mov edx, DWORD PTR [esp+12]
22:
	movzx ebx, BYTE PTR [edx]
	mov BYTE PTR [eax+32], bl
	add edx, 1
	add eax, 1
	sub ecx, 1
	jne 22b
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [eax]
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 1779033703
	mov DWORD PTR [eax], ecx
	mov ecx, -1150833019
	mov DWORD PTR [eax+4], ecx
	mov ecx, 1013904242
	mov DWORD PTR [eax+8], ecx
	mov ecx, -1521486534
	mov DWORD PTR [eax+12], ecx
	mov ecx, 1359893119
	mov DWORD PTR [eax+16], ecx
	mov ecx, -1694144372
	mov DWORD PTR [eax+20], ecx
	mov ecx, 528734635
	mov DWORD PTR [eax+24], ecx
	mov ecx, 1541459225
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [eax]
	xor ecx, 16842752
	mov edx, DWORD PTR [esp+16]
	ror edx, 24
	xor ecx, edx
	xor ecx, DWORD PTR [esp+8]
	mov DWORD PTR [eax], ecx
	ret
	.p2align 6

vg_blake2s_update:
	lea esp, [esp-604]
	mov eax, DWORD PTR [esp+608]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+528], eax
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+532], ecx
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 63
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	test edi, edi
	je 22f
	test eax, eax
	je 24f
	mov ecx, 64
	sub ecx, eax
	cmp edi, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, edi
27:
	sub edi, ecx
	mov edx, ebx
	add edx, eax
	mov eax, DWORD PTR [ebp+528]
	add eax, ecx
	mov DWORD PTR [ebp+528], eax
	mov eax, DWORD PTR [ebp+532]
	adc eax, 0
	mov DWORD PTR [ebp+532], eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+32], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	test edi, edi
	je 211f
	mov DWORD PTR [ebp+536], esi
	mov DWORD PTR [ebp+540], edi
	mov esi, ebx
	add esi, 32
	mov edi, 1
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2s_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebp+536]
	mov edi, DWORD PTR [ebp+540]
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test edi, edi
	je 213f
	mov eax, edi
	sub eax, 1
	mov ecx, eax
	and ecx, 63
	sub eax, ecx
	je 215f
	mov DWORD PTR [ebp+540], edi
	mov DWORD PTR [ebp+544], eax
	mov edi, eax
	shr edi, 6
	mov ecx, DWORD PTR [ebp+528]
	add ecx, 64
	mov edx, DWORD PTR [ebp+532]
	adc edx, 0
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2s_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+544]
	add esi, eax
	mov edi, DWORD PTR [ebp+540]
	sub edi, eax
	jmp 216f
215:
216:
	mov ecx, edi
	mov edx, ebx
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+32], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	lea esp, [esp+604]
	ret
	.p2align 6

vg_blake2s_finalize:
	lea esp, [esp-600]
	mov eax, DWORD PTR [esp+604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 63
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov edx, ebx
	add edx, eax
	mov ecx, 64
	sub ecx, eax
	mov eax, 0
	je 22f
24:
	mov BYTE PTR [edx+32], al
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, ebx
	add esi, 32
	mov edi, 1
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2s_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	mov DWORD PTR [eax+28], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	lea esp, [esp+600]
	ret
	.p2align 6
