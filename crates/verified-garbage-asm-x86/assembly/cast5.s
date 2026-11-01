// The functions of `src/cast5.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+64], ebx
	mov DWORD PTR [eax+72], edi
	mov DWORD PTR [eax+76], ebp
	mov DWORD PTR [eax+68], esi
	mov esi, eax
	mov edi, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ecx, 0
	mov DWORD PTR [esi+16], ecx
	mov DWORD PTR [esi+20], ecx
	mov DWORD PTR [esi+24], ecx
	mov DWORD PTR [esi+28], ecx
	add eax, 16
20:
	movzx ecx, BYTE PTR [edi]
	mov BYTE PTR [eax], cl
	add edi, 1
	add eax, 1
	sub ebx, 1
	jne 20b
	mov edi, edx
	mov ebx, 2
21:
	movzx ecx, BYTE PTR [esi+26]
	movzx edx, BYTE PTR [esi+24]
	movzx eax, BYTE PTR [esi+27]
	movzx ebp, BYTE PTR [esi+25]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
22:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 22b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+30]
	movzx edx, BYTE PTR [esi+28]
	movzx eax, BYTE PTR [esi+31]
	movzx ebp, BYTE PTR [esi+29]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
23:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 23b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+16]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+32], eax
	movzx ecx, BYTE PTR [esi+35]
	movzx edx, BYTE PTR [esi+33]
	movzx eax, BYTE PTR [esi+34]
	movzx ebp, BYTE PTR [esi+32]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
24:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 24b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+24]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+36], eax
	movzx ecx, BYTE PTR [esi+36]
	movzx edx, BYTE PTR [esi+37]
	movzx eax, BYTE PTR [esi+38]
	movzx ebp, BYTE PTR [esi+39]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
25:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 25b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+28]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+40], eax
	movzx ecx, BYTE PTR [esi+40]
	movzx edx, BYTE PTR [esi+43]
	movzx eax, BYTE PTR [esi+41]
	movzx ebp, BYTE PTR [esi+42]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
26:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 26b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+20]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+44], eax
	movzx ecx, BYTE PTR [esi+44]
	movzx edx, BYTE PTR [esi+41]
	movzx eax, BYTE PTR [esi+38]
	movzx ebp, BYTE PTR [esi+34]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
27:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 27b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+38]
	movzx edx, BYTE PTR [esi+39]
	movzx eax, BYTE PTR [esi+41]
	movzx ebp, BYTE PTR [esi+40]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
28:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 28b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi], eax
	movzx ecx, BYTE PTR [esi+36]
	movzx edx, BYTE PTR [esi+37]
	movzx eax, BYTE PTR [esi+43]
	movzx ebp, BYTE PTR [esi+42]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
29:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 29b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+4], eax
	movzx ecx, BYTE PTR [esi+34]
	movzx edx, BYTE PTR [esi+35]
	movzx eax, BYTE PTR [esi+45]
	movzx ebp, BYTE PTR [esi+44]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
210:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 210b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+8], eax
	movzx ecx, BYTE PTR [esi+32]
	movzx edx, BYTE PTR [esi+33]
	movzx eax, BYTE PTR [esi+47]
	movzx ebp, BYTE PTR [esi+46]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
211:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 211b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+12], eax
	movzx ecx, BYTE PTR [esi+34]
	movzx edx, BYTE PTR [esi+32]
	movzx eax, BYTE PTR [esi+35]
	movzx ebp, BYTE PTR [esi+33]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
212:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 212b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+38]
	movzx edx, BYTE PTR [esi+36]
	movzx eax, BYTE PTR [esi+39]
	movzx ebp, BYTE PTR [esi+37]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
213:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 213b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+40]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+16], eax
	movzx ecx, BYTE PTR [esi+19]
	movzx edx, BYTE PTR [esi+17]
	movzx eax, BYTE PTR [esi+18]
	movzx ebp, BYTE PTR [esi+16]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
214:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 214b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+32]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+20], eax
	movzx ecx, BYTE PTR [esi+20]
	movzx edx, BYTE PTR [esi+21]
	movzx eax, BYTE PTR [esi+22]
	movzx ebp, BYTE PTR [esi+23]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
215:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 215b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+36]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+24], eax
	movzx ecx, BYTE PTR [esi+24]
	movzx edx, BYTE PTR [esi+27]
	movzx eax, BYTE PTR [esi+25]
	movzx ebp, BYTE PTR [esi+26]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
216:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 216b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+44]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+28], eax
	movzx ecx, BYTE PTR [esi+23]
	movzx edx, BYTE PTR [esi+19]
	movzx eax, BYTE PTR [esi+29]
	movzx ebp, BYTE PTR [esi+24]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
217:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 217b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+29]
	movzx edx, BYTE PTR [esi+28]
	movzx eax, BYTE PTR [esi+18]
	movzx ebp, BYTE PTR [esi+19]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
218:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 218b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+16], eax
	movzx ecx, BYTE PTR [esi+31]
	movzx edx, BYTE PTR [esi+30]
	movzx eax, BYTE PTR [esi+16]
	movzx ebp, BYTE PTR [esi+17]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
219:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 219b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+20], eax
	movzx ecx, BYTE PTR [esi+25]
	movzx edx, BYTE PTR [esi+24]
	movzx eax, BYTE PTR [esi+22]
	movzx ebp, BYTE PTR [esi+23]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
220:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 220b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+24], eax
	movzx ecx, BYTE PTR [esi+27]
	movzx edx, BYTE PTR [esi+26]
	movzx eax, BYTE PTR [esi+20]
	movzx ebp, BYTE PTR [esi+21]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
221:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 221b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+28], eax
	movzx ecx, BYTE PTR [esi+26]
	movzx edx, BYTE PTR [esi+24]
	movzx eax, BYTE PTR [esi+27]
	movzx ebp, BYTE PTR [esi+25]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
222:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 222b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+30]
	movzx edx, BYTE PTR [esi+28]
	movzx eax, BYTE PTR [esi+31]
	movzx ebp, BYTE PTR [esi+29]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
223:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 223b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+16]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+32], eax
	movzx ecx, BYTE PTR [esi+35]
	movzx edx, BYTE PTR [esi+33]
	movzx eax, BYTE PTR [esi+34]
	movzx ebp, BYTE PTR [esi+32]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
224:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 224b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+24]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+36], eax
	movzx ecx, BYTE PTR [esi+36]
	movzx edx, BYTE PTR [esi+37]
	movzx eax, BYTE PTR [esi+38]
	movzx ebp, BYTE PTR [esi+39]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
225:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 225b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+28]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+40], eax
	movzx ecx, BYTE PTR [esi+40]
	movzx edx, BYTE PTR [esi+43]
	movzx eax, BYTE PTR [esi+41]
	movzx ebp, BYTE PTR [esi+42]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
226:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 226b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+20]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+44], eax
	movzx ecx, BYTE PTR [esi+38]
	movzx edx, BYTE PTR [esi+34]
	movzx eax, BYTE PTR [esi+44]
	movzx ebp, BYTE PTR [esi+41]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
227:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 227b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+45]
	movzx edx, BYTE PTR [esi+44]
	movzx eax, BYTE PTR [esi+34]
	movzx ebp, BYTE PTR [esi+35]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
228:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 228b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+32], eax
	movzx ecx, BYTE PTR [esi+47]
	movzx edx, BYTE PTR [esi+46]
	movzx eax, BYTE PTR [esi+32]
	movzx ebp, BYTE PTR [esi+33]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
229:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 229b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+36], eax
	movzx ecx, BYTE PTR [esi+41]
	movzx edx, BYTE PTR [esi+40]
	movzx eax, BYTE PTR [esi+38]
	movzx ebp, BYTE PTR [esi+39]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
230:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 230b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+40], eax
	movzx ecx, BYTE PTR [esi+43]
	movzx edx, BYTE PTR [esi+42]
	movzx eax, BYTE PTR [esi+36]
	movzx ebp, BYTE PTR [esi+37]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
231:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 231b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+44], eax
	movzx ecx, BYTE PTR [esi+34]
	movzx edx, BYTE PTR [esi+32]
	movzx eax, BYTE PTR [esi+35]
	movzx ebp, BYTE PTR [esi+33]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
232:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 232b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+38]
	movzx edx, BYTE PTR [esi+36]
	movzx eax, BYTE PTR [esi+39]
	movzx ebp, BYTE PTR [esi+37]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
233:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 233b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+40]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+16], eax
	movzx ecx, BYTE PTR [esi+19]
	movzx edx, BYTE PTR [esi+17]
	movzx eax, BYTE PTR [esi+18]
	movzx ebp, BYTE PTR [esi+16]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
234:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 234b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+32]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+20], eax
	movzx ecx, BYTE PTR [esi+20]
	movzx edx, BYTE PTR [esi+21]
	movzx eax, BYTE PTR [esi+22]
	movzx ebp, BYTE PTR [esi+23]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
235:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 235b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+36]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+24], eax
	movzx ecx, BYTE PTR [esi+24]
	movzx edx, BYTE PTR [esi+27]
	movzx eax, BYTE PTR [esi+25]
	movzx ebp, BYTE PTR [esi+26]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
236:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 236b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+44]
	bswap ecx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esi+28], eax
	movzx ecx, BYTE PTR [esi+29]
	movzx edx, BYTE PTR [esi+24]
	movzx eax, BYTE PTR [esi+23]
	movzx ebp, BYTE PTR [esi+19]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
237:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 237b
	movdqu XMMWORD PTR [esi+48], xmm1
	movzx ecx, BYTE PTR [esi+22]
	movzx edx, BYTE PTR [esi+23]
	movzx eax, BYTE PTR [esi+25]
	movzx ebp, BYTE PTR [esi+24]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
238:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 238b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+48], eax
	movzx ecx, BYTE PTR [esi+20]
	movzx edx, BYTE PTR [esi+21]
	movzx eax, BYTE PTR [esi+27]
	movzx ebp, BYTE PTR [esi+26]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
239:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 239b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+52], eax
	movzx ecx, BYTE PTR [esi+18]
	movzx edx, BYTE PTR [esi+19]
	movzx eax, BYTE PTR [esi+29]
	movzx ebp, BYTE PTR [esi+28]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
240:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 240b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+56], eax
	movzx ecx, BYTE PTR [esi+16]
	movzx edx, BYTE PTR [esi+17]
	movzx eax, BYTE PTR [esi+31]
	movzx ebp, BYTE PTR [esi+30]
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, eax
	movd xmm5, ebp
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S5678}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
241:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 241b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+60], eax
	add edi, 64
	sub ebx, 1
	jne 21b
	mov ebx, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+72]
	mov ebp, DWORD PTR [esi+76]
	mov esi, DWORD PTR [esi+68]
	ret
	.p2align 6

vg_cast5_ecb_encrypt:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+40], edi
	mov DWORD PTR [eax+44], ebp
	mov DWORD PTR [eax+36], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov DWORD PTR [esi+48], ecx
	mov DWORD PTR [esi+52], edx
	mov DWORD PTR [esi+56], edi
	mov DWORD PTR [esi+60], ebx
	cmp ebx, 0
	je 20f
22:
	mov edx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [edx]
	bswap ebx
	mov ebp, DWORD PTR [edx+4]
	bswap ebp
	mov edx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+64], edx
	mov ecx, DWORD PTR [esi+52]
	shr ecx, 2
	add ecx, 1
	mov DWORD PTR [esi+68], ecx
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
23:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
24:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 24b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	xor eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
25:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 25b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	sub eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	sub eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
26:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 26b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+4]
	sub eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	mov DWORD PTR [esi+68], edx
	jne 23b
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
	je 27f
	jmp 28f
27:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
29:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 29b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	add edx, 4
	mov DWORD PTR [esi+64], edx
28:
	mov edx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+60]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+56], edx
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+52], ecx
	mov DWORD PTR [esi+60], edi
	mov edx, DWORD PTR [esi+56]
	add edx, 8
	mov DWORD PTR [esi+56], edx
	mov edx, DWORD PTR [esi+60]
	sub edx, 1
	mov DWORD PTR [esi+60], edx
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esi+32]
	mov edi, DWORD PTR [esi+40]
	mov ebp, DWORD PTR [esi+44]
	mov esi, DWORD PTR [esi+36]
	ret
	.p2align 6

vg_cast5_ecb_decrypt:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+32], ebx
	mov DWORD PTR [eax+40], edi
	mov DWORD PTR [eax+44], ebp
	mov DWORD PTR [eax+36], esi
	mov esi, eax
	mov ecx, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov DWORD PTR [esi+48], ecx
	mov DWORD PTR [esi+52], edx
	mov DWORD PTR [esi+56], edi
	mov DWORD PTR [esi+60], ebx
	cmp ebx, 0
	je 20f
22:
	mov edx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [edx]
	bswap ebx
	mov ebp, DWORD PTR [edx+4]
	bswap ebp
	mov edx, DWORD PTR [esi+52]
	add edx, edx
	add edx, edx
	mov ecx, DWORD PTR [esi+48]
	add edx, ecx
	sub edx, 4
	mov DWORD PTR [esi+64], edx
	mov ecx, DWORD PTR [esi+52]
	shr ecx, 2
	add ecx, 1
	mov DWORD PTR [esi+68], ecx
	mov ecx, DWORD PTR [esi+52]
	cmp ecx, 16
	je 23f
	jmp 24f
23:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
25:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 25b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	sub edx, 4
	mov DWORD PTR [esi+64], edx
24:
26:
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	sub eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
27:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 27b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+4]
	sub eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	sub edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	xor eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
28:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 28b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	sub eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	sub edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+64]
	mov eax, DWORD PTR [edx]
	add eax, ebp
	mov ecx, DWORD PTR [edx+64]
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 31
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 30
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 28
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 24
	xor eax, edi
	and eax, edx
	xor eax, edi
	shr ecx, 1
	mov edx, ecx
	and edx, 1
	sub edx, 1
	mov edi, eax
	ror edi, 16
	xor eax, edi
	and eax, edx
	xor eax, edi
	mov ecx, eax
	and ecx, 255
	mov edx, eax
	shr edx, 8
	and edx, 255
	mov edi, eax
	shr edi, 16
	and edi, 255
	shr eax, 24
	movd xmm0, ecx
	movd xmm4, edx
	punpckldq xmm0, xmm4
	movd xmm4, edi
	movd xmm5, eax
	punpckldq xmm4, xmm5
	punpcklqdq xmm0, xmm4
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAST5_S1234}
	pop ecx
	mov ecx, eax
	mov edx, 64
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov eax, 1
	movd xmm3, eax
	pshufd xmm3, xmm3, 0
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
29:
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [ecx+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	add ecx, 64
	sub edx, 1
	jne 29b
	movdqu XMMWORD PTR [esi], xmm1
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+8]
	sub eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi]
	xor eax, ebx
	mov ebx, ebp
	mov ebp, eax
	mov edx, DWORD PTR [esi+64]
	sub edx, 4
	mov DWORD PTR [esi+64], edx
	mov edx, DWORD PTR [esi+68]
	sub edx, 1
	mov DWORD PTR [esi+68], edx
	jne 26b
	mov edx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+60]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+56], edx
	mov DWORD PTR [esi+48], eax
	mov DWORD PTR [esi+52], ecx
	mov DWORD PTR [esi+60], edi
	mov edx, DWORD PTR [esi+56]
	add edx, 8
	mov DWORD PTR [esi+56], edx
	mov edx, DWORD PTR [esi+60]
	sub edx, 1
	mov DWORD PTR [esi+60], edx
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esi+32]
	mov edi, DWORD PTR [esi+40]
	mov ebp, DWORD PTR [esi+44]
	mov esi, DWORD PTR [esi+36]
	ret
	.p2align 6
