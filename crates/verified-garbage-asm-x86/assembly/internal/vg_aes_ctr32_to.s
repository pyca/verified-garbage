// The functions of `src/internal/vg_aes_ctr32_to.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_to:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+304], ebx
	mov DWORD PTR [eax+308], esi
	mov DWORD PTR [eax+312], edi
	mov DWORD PTR [eax+316], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+320], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+324], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+328], eax
	mov eax, DWORD PTR [ecx+12]
	bswap eax
	mov DWORD PTR [edi+332], eax
	add eax, DWORD PTR [esp+20]
	bswap eax
	mov DWORD PTR [ecx+12], eax
	mov ecx, 252645135
	movd xmm0, ecx
	pshufd xmm0, xmm0, 0
	movdqu XMMWORD PTR [edi], xmm0
	mov ecx, 858993459
	movd xmm0, ecx
	pshufd xmm0, xmm0, 0
	movdqu XMMWORD PTR [edi+16], xmm0
	mov ecx, 1431655765
	movd xmm0, ecx
	pshufd xmm0, xmm0, 0
	movdqu XMMWORD PTR [edi+32], xmm0
	mov ecx, -16711936
	movd xmm0, ecx
	pshufd xmm0, xmm0, 68
	movdqu XMMWORD PTR [edi+48], xmm0
	mov ecx, -1
	movd xmm0, ecx
	pshufd xmm0, xmm0, 17
	movdqu XMMWORD PTR [edi+64], xmm0
	mov ecx, 1667457891
	movd xmm0, ecx
	pshufd xmm0, xmm0, 0
	movdqu XMMWORD PTR [edi+80], xmm0
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ecx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, edx
	add edx, eax
	movdqu xmm0, XMMWORD PTR [edx]
	movdqu xmm1, XMMWORD PTR [edi+80]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+288], xmm0
	shr ecx, 1
	add eax, 16
	mov edx, edi
	add edx, 384
20:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [edi+80]
	pxor xmm0, xmm1
	pshufd xmm0, xmm0, 216
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqu xmm2, XMMWORD PTR [edi+48]
	movdqa xmm1, xmm0
	psrlq xmm1, 24
	pxor xmm1, xmm0
	pand xmm1, xmm2
	pxor xmm0, xmm1
	psllq xmm1, 24
	pxor xmm0, xmm1
	pshufhw xmm0, xmm0, 177
	movdqu xmm3, XMMWORD PTR [edi+64]
	movdqa xmm1, xmm0
	pslld xmm1, 8
	movdqa xmm2, xmm0
	psrld xmm2, 24
	pxor xmm1, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm3
	pxor xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [edi]
	movdqu xmm6, XMMWORD PTR [edi+16]
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqa xmm1, xmm0
	pand xmm1, xmm5
	pxor xmm0, xmm1
	movdqa xmm4, xmm1
	psllq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 4
	pxor xmm0, xmm4
	movdqa xmm2, xmm1
	pand xmm2, xmm6
	pxor xmm1, xmm2
	movdqa xmm4, xmm2
	psllq xmm4, 2
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm1, xmm4
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edx], xmm3
	movdqu XMMWORD PTR [edx+16], xmm2
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pxor xmm1, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 1
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edx+32], xmm3
	movdqu XMMWORD PTR [edx+48], xmm1
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm4, xmm2
	psllq xmm4, 2
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edx+64], xmm3
	movdqu XMMWORD PTR [edx+80], xmm2
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	pxor xmm0, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edx+96], xmm3
	movdqu XMMWORD PTR [edx+112], xmm0
	add eax, 16
	add edx, 128
	sub ecx, 1
	je 21f
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [edi+80]
	pxor xmm0, xmm1
	pshufd xmm0, xmm0, 216
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqu xmm2, XMMWORD PTR [edi+48]
	movdqa xmm1, xmm0
	psrlq xmm1, 24
	pxor xmm1, xmm0
	pand xmm1, xmm2
	pxor xmm0, xmm1
	psllq xmm1, 24
	pxor xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [edi]
	movdqu xmm6, XMMWORD PTR [edi+16]
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqa xmm1, xmm0
	pand xmm1, xmm5
	pxor xmm0, xmm1
	movdqa xmm4, xmm1
	psllq xmm4, 4
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 4
	pxor xmm0, xmm4
	movdqa xmm2, xmm1
	pand xmm2, xmm6
	pxor xmm1, xmm2
	movdqa xmm4, xmm2
	psllq xmm4, 2
	pxor xmm2, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm1, xmm4
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edx], xmm3
	movdqu XMMWORD PTR [edx+16], xmm2
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pxor xmm1, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 1
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edx+32], xmm3
	movdqu XMMWORD PTR [edx+48], xmm1
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm4, xmm2
	psllq xmm4, 2
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	pxor xmm2, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edx+64], xmm3
	movdqu XMMWORD PTR [edx+80], xmm2
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	pxor xmm0, xmm3
	movdqa xmm4, xmm3
	psllq xmm4, 1
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edx+96], xmm3
	movdqu XMMWORD PTR [edx+112], xmm0
	add eax, 16
	add edx, 128
	test ecx, ecx
	jmp 22f
21:
22:
	jne 20b
	mov edx, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+28]
	mov ebp, DWORD PTR [esp+20]
	test ebp, ebp
	je 23f
25:
	movdqu xmm1, XMMWORD PTR [edi+320]
	pslldq xmm1, 4
	psrldq xmm1, 4
	mov esi, DWORD PTR [edi+332]
	mov eax, esi
	add eax, 0
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	mov eax, esi
	add eax, 1
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	mov eax, esi
	add eax, 2
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	mov eax, esi
	add eax, 3
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	mov eax, esi
	add eax, 4
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+64], xmm0
	mov eax, esi
	add eax, 5
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	mov eax, esi
	add eax, 6
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+96], xmm0
	mov eax, esi
	add eax, 7
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm1
	movdqu XMMWORD PTR [edi+112], xmm0
	add esi, 8
	mov DWORD PTR [edi+332], esi
	mov eax, DWORD PTR [esp+4]
	mov ecx, 16711935
	movd xmm5, ecx
	pshufd xmm5, xmm5, 0
	mov ecx, 1431655765
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	mov ecx, 858993459
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [eax]
	pxor xmm0, xmm4
	pxor xmm1, xmm4
	pxor xmm2, xmm4
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm5
	pxor xmm1, xmm4
	psllq xmm4, 8
	pxor xmm0, xmm4
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm4
	punpckhqdq xmm1, xmm4
	movdqa xmm4, xmm2
	punpcklwd xmm2, xmm3
	punpckhwd xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm4
	punpckhwd xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 8
	pxor xmm4, xmm3
	pand xmm4, xmm5
	pxor xmm3, xmm4
	psllq xmm4, 8
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklqdq xmm2, xmm4
	punpckhqdq xmm3, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm4, xmm1
	pand xmm4, xmm6
	pxor xmm1, xmm4
	psllq xmm4, 1
	pxor xmm0, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm4, xmm2
	pand xmm4, xmm7
	pxor xmm2, xmm4
	psllq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm4, xmm3
	pand xmm4, xmm7
	pxor xmm3, xmm4
	psllq xmm4, 2
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+16], xmm1
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [edi+80]
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [edi+112]
	movdqu xmm4, XMMWORD PTR [eax]
	pxor xmm0, xmm4
	pxor xmm1, xmm4
	pxor xmm2, xmm4
	pxor xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm5
	pxor xmm1, xmm4
	psllq xmm4, 8
	pxor xmm0, xmm4
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm4
	punpckhqdq xmm1, xmm4
	movdqa xmm4, xmm2
	punpcklwd xmm2, xmm3
	punpckhwd xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm4
	punpckhwd xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 8
	pxor xmm4, xmm3
	pand xmm4, xmm5
	pxor xmm3, xmm4
	psllq xmm4, 8
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklqdq xmm2, xmm4
	punpckhqdq xmm3, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm4, xmm1
	pand xmm4, xmm6
	pxor xmm1, xmm4
	psllq xmm4, 1
	pxor xmm0, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm4, xmm2
	pand xmm4, xmm7
	pxor xmm2, xmm4
	psllq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm4, xmm3
	pand xmm4, xmm7
	pxor xmm3, xmm4
	psllq xmm4, 2
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+112], xmm3
	mov ecx, 252645135
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm0
	psrlq xmm5, 4
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	psllq xmm5, 4
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm1
	psrlq xmm5, 4
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	psllq xmm5, 4
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	movdqa xmm5, xmm2
	psrlq xmm5, 4
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	psllq xmm5, 4
	pxor xmm2, xmm5
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+112]
	movdqa xmm5, xmm3
	psrlq xmm5, 4
	pxor xmm5, xmm4
	pand xmm5, xmm6
	pxor xmm4, xmm5
	psllq xmm5, 4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+112], xmm4
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 1
	mov eax, edi
	add eax, 384
26:
	movdqu xmm4, XMMWORD PTR [edi+80]
	pxor xmm2, xmm4
	movdqa xmm5, xmm2
	pxor xmm5, xmm1
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm5
	pxor xmm3, xmm6
	movdqu xmm7, XMMWORD PTR [edi+112]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi], xmm6
	movdqa xmm6, xmm3
	pxor xmm6, xmm2
	pxor xmm0, xmm5
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [edi+16], xmm7
	movdqa xmm7, xmm6
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi+64]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm7
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+112]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+144], xmm4
	movdqa xmm4, xmm6
	pand xmm4, xmm7
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm1
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu xmm7, XMMWORD PTR [edi+16]
	pand xmm7, xmm1
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+192], xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm3
	movdqu XMMWORD PTR [edi+208], xmm3
	movdqa xmm3, xmm6
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm6, XMMWORD PTR [edi+128]
	pand xmm6, xmm3
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [edi+240], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pand xmm3, xmm5
	pxor xmm7, xmm6
	pxor xmm7, xmm4
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pand xmm2, xmm0
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+96]
	pxor xmm3, xmm0
	pxor xmm1, xmm2
	pxor xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [edi+144]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm2
	movdqu XMMWORD PTR [edi+256], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pand xmm0, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	movdqu XMMWORD PTR [edi+272], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pand xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [edi+96]
	pand xmm6, xmm2
	pxor xmm1, xmm6
	pxor xmm0, xmm4
	movdqa xmm4, xmm3
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm0, xmm6
	pxor xmm2, xmm5
	pxor xmm1, xmm2
	movdqa xmm2, xmm1
	pxor xmm2, xmm4
	pxor xmm4, xmm0
	movdqa xmm6, xmm7
	pxor xmm6, xmm0
	pand xmm2, xmm6
	pxor xmm2, xmm0
	pxor xmm3, xmm1
	pxor xmm7, xmm2
	movdqa xmm6, xmm4
	pxor xmm6, xmm2
	pand xmm6, xmm0
	pxor xmm7, xmm6
	pand xmm5, xmm2
	pxor xmm6, xmm4
	pand xmm4, xmm3
	pxor xmm4, xmm1
	movdqu xmm0, XMMWORD PTR [edi+16]
	pand xmm0, xmm4
	pand xmm6, xmm4
	pxor xmm6, xmm3
	movdqa xmm1, xmm4
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi]
	pand xmm3, xmm7
	movdqu XMMWORD PTR [edi], xmm2
	movdqu xmm2, XMMWORD PTR [edi+128]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+192]
	pand xmm0, xmm4
	pxor xmm4, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu xmm5, XMMWORD PTR [edi+240]
	pand xmm5, xmm6
	pxor xmm0, xmm3
	pxor xmm6, xmm7
	movdqu XMMWORD PTR [edi+128], xmm3
	movdqu xmm3, XMMWORD PTR [edi+176]
	pand xmm3, xmm4
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+80]
	pand xmm2, xmm1
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+80], xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pand xmm2, xmm1
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu xmm3, XMMWORD PTR [edi+272]
	pand xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+224]
	pand xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pand xmm3, xmm1
	pxor xmm3, xmm5
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	pxor xmm2, xmm0
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edi+16]
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+176], xmm2
	movdqu xmm2, XMMWORD PTR [edi+256]
	pand xmm2, xmm7
	pxor xmm6, xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pxor xmm7, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm2, xmm5
	pxor xmm6, xmm2
	movdqu xmm5, XMMWORD PTR [edi+16]
	pxor xmm5, xmm3
	pxor xmm2, xmm4
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+144]
	pand xmm2, xmm7
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+96]
	pand xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi+208]
	pand xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pxor xmm2, xmm1
	movdqu xmm4, XMMWORD PTR [edi+48]
	pxor xmm2, xmm4
	pxor xmm1, xmm5
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm7, xmm2
	movdqu xmm4, XMMWORD PTR [edi+128]
	pxor xmm4, xmm1
	pxor xmm1, xmm3
	pxor xmm2, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [edi+80]
	pxor xmm1, xmm4
	pshufd xmm4, xmm2, 57
	movdqu XMMWORD PTR [edi], xmm5
	movdqa xmm5, xmm4
	psrld xmm5, 8
	pslld xmm4, 24
	pxor xmm4, xmm5
	pxor xmm2, xmm4
	pshufd xmm5, xmm2, 78
	pshuflw xmm5, xmm5, 177
	pshufhw xmm5, xmm5, 177
	movdqu XMMWORD PTR [edi+16], xmm2
	pshufd xmm2, xmm1, 57
	pxor xmm5, xmm4
	movdqa xmm4, xmm2
	psrld xmm4, 8
	pslld xmm2, 24
	pxor xmm4, xmm2
	pxor xmm1, xmm4
	pshufd xmm2, xmm1, 78
	pxor xmm1, xmm5
	movdqu xmm5, XMMWORD PTR [eax+112]
	pxor xmm1, xmm5
	pshufd xmm5, xmm0, 57
	pshuflw xmm2, xmm2, 177
	movdqu XMMWORD PTR [edi+112], xmm1
	movdqa xmm1, xmm5
	psrld xmm1, 8
	pshufhw xmm2, xmm2, 177
	pxor xmm2, xmm4
	pslld xmm5, 24
	pshufd xmm4, xmm6, 57
	pxor xmm5, xmm1
	movdqa xmm1, xmm4
	pslld xmm1, 24
	psrld xmm4, 8
	pxor xmm0, xmm5
	pxor xmm2, xmm0
	pxor xmm4, xmm1
	pshufd xmm0, xmm0, 78
	movdqu xmm1, XMMWORD PTR [eax+96]
	pxor xmm2, xmm1
	pshufd xmm1, xmm3, 57
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqa xmm2, xmm1
	psrld xmm2, 8
	pslld xmm1, 24
	pxor xmm2, xmm1
	pshuflw xmm0, xmm0, 177
	pshufd xmm1, xmm7, 57
	pshufhw xmm0, xmm0, 177
	pxor xmm3, xmm2
	pxor xmm5, xmm0
	pshufd xmm0, xmm6, 78
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	pslld xmm4, 24
	psrld xmm1, 8
	pxor xmm1, xmm4
	pshufd xmm4, xmm3, 78
	pxor xmm7, xmm1
	pshuflw xmm4, xmm4, 177
	pxor xmm0, xmm7
	pshufd xmm7, xmm7, 78
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	pxor xmm1, xmm7
	pxor xmm3, xmm1
	pshufhw xmm4, xmm4, 177
	pxor xmm5, xmm6
	movdqu xmm1, XMMWORD PTR [eax+80]
	pxor xmm5, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [edi]
	pshufd xmm4, xmm1, 57
	movdqa xmm6, xmm4
	pslld xmm6, 24
	psrld xmm4, 8
	pxor xmm4, xmm6
	pxor xmm1, xmm4
	pshufd xmm6, xmm1, 78
	movdqu xmm7, XMMWORD PTR [edi+16]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+80], xmm5
	movdqu xmm5, XMMWORD PTR [eax+64]
	pxor xmm0, xmm5
	pshuflw xmm6, xmm6, 177
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [edi+176]
	pshufd xmm5, xmm1, 57
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqa xmm0, xmm5
	pslld xmm0, 24
	psrld xmm5, 8
	pxor xmm0, xmm5
	pxor xmm1, xmm0
	pxor xmm3, xmm7
	pshufd xmm5, xmm1, 78
	pshufhw xmm6, xmm6, 177
	pxor xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [eax+32]
	pxor xmm2, xmm4
	pshuflw xmm5, xmm5, 177
	pshufhw xmm5, xmm5, 177
	movdqu xmm4, XMMWORD PTR [eax+48]
	pxor xmm3, xmm4
	pxor xmm0, xmm5
	pxor xmm1, xmm7
	pxor xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [eax+16]
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [eax]
	pxor xmm0, xmm4
	add eax, 128
	sub ecx, 1
	je 27f
	movdqu xmm4, XMMWORD PTR [edi+80]
	pxor xmm2, xmm4
	movdqa xmm5, xmm2
	pxor xmm5, xmm1
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm5
	pxor xmm3, xmm6
	movdqu xmm7, XMMWORD PTR [edi+112]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi], xmm6
	movdqa xmm6, xmm3
	pxor xmm6, xmm2
	pxor xmm0, xmm5
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [edi+16], xmm7
	movdqa xmm7, xmm6
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi+64]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm7
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+112]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+144], xmm4
	movdqa xmm4, xmm6
	pand xmm4, xmm7
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm1
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu xmm7, XMMWORD PTR [edi+16]
	pand xmm7, xmm1
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+192], xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm3
	movdqu XMMWORD PTR [edi+208], xmm3
	movdqa xmm3, xmm6
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm6, XMMWORD PTR [edi+128]
	pand xmm6, xmm3
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [edi+240], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pand xmm3, xmm5
	pxor xmm7, xmm6
	pxor xmm7, xmm4
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pand xmm2, xmm0
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+96]
	pxor xmm3, xmm0
	pxor xmm1, xmm2
	pxor xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [edi+144]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm2
	movdqu XMMWORD PTR [edi+256], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pand xmm0, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	movdqu XMMWORD PTR [edi+272], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pand xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [edi+96]
	pand xmm6, xmm2
	pxor xmm1, xmm6
	pxor xmm0, xmm4
	movdqa xmm4, xmm3
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm0, xmm6
	pxor xmm2, xmm5
	pxor xmm1, xmm2
	movdqa xmm2, xmm1
	pxor xmm2, xmm4
	pxor xmm4, xmm0
	movdqa xmm6, xmm7
	pxor xmm6, xmm0
	pand xmm2, xmm6
	pxor xmm2, xmm0
	pxor xmm3, xmm1
	pxor xmm7, xmm2
	movdqa xmm6, xmm4
	pxor xmm6, xmm2
	pand xmm6, xmm0
	pxor xmm7, xmm6
	pand xmm5, xmm2
	pxor xmm6, xmm4
	pand xmm4, xmm3
	pxor xmm4, xmm1
	movdqu xmm0, XMMWORD PTR [edi+16]
	pand xmm0, xmm4
	pand xmm6, xmm4
	pxor xmm6, xmm3
	movdqa xmm1, xmm4
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi]
	pand xmm3, xmm7
	movdqu XMMWORD PTR [edi], xmm2
	movdqu xmm2, XMMWORD PTR [edi+128]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+192]
	pand xmm0, xmm4
	pxor xmm4, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu xmm5, XMMWORD PTR [edi+240]
	pand xmm5, xmm6
	pxor xmm0, xmm3
	pxor xmm6, xmm7
	movdqu XMMWORD PTR [edi+128], xmm3
	movdqu xmm3, XMMWORD PTR [edi+176]
	pand xmm3, xmm4
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+80]
	pand xmm2, xmm1
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+80], xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pand xmm2, xmm1
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu xmm3, XMMWORD PTR [edi+272]
	pand xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+224]
	pand xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pand xmm3, xmm1
	pxor xmm3, xmm5
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	pxor xmm2, xmm0
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edi+16]
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+176], xmm2
	movdqu xmm2, XMMWORD PTR [edi+256]
	pand xmm2, xmm7
	pxor xmm6, xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pxor xmm7, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm2, xmm5
	pxor xmm6, xmm2
	movdqu xmm5, XMMWORD PTR [edi+16]
	pxor xmm5, xmm3
	pxor xmm2, xmm4
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+144]
	pand xmm2, xmm7
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+96]
	pand xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi+208]
	pand xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pxor xmm2, xmm1
	movdqu xmm4, XMMWORD PTR [edi+48]
	pxor xmm2, xmm4
	pxor xmm1, xmm5
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm7, xmm2
	movdqu xmm4, XMMWORD PTR [edi+128]
	pxor xmm4, xmm1
	pxor xmm1, xmm3
	pxor xmm2, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [edi+80]
	pxor xmm1, xmm4
	pshuflw xmm2, xmm2, 180
	pshuflw xmm7, xmm7, 180
	pshufhw xmm2, xmm2, 180
	pshufd xmm4, xmm2, 57
	pshuflw xmm1, xmm1, 180
	pshuflw xmm3, xmm3, 180
	pxor xmm2, xmm4
	pshufhw xmm1, xmm1, 180
	movdqu XMMWORD PTR [edi], xmm5
	pshufd xmm5, xmm2, 78
	pshuflw xmm0, xmm0, 180
	pxor xmm4, xmm5
	pshufd xmm5, xmm1, 57
	pshufhw xmm7, xmm7, 180
	pxor xmm1, xmm5
	pxor xmm4, xmm1
	pshufhw xmm0, xmm0, 180
	pshufd xmm1, xmm1, 78
	pxor xmm5, xmm1
	pshuflw xmm6, xmm6, 180
	movdqu xmm1, XMMWORD PTR [eax+112]
	pxor xmm4, xmm1
	pshufd xmm1, xmm0, 57
	pxor xmm0, xmm1
	pxor xmm5, xmm0
	pshufd xmm0, xmm0, 78
	pshufhw xmm6, xmm6, 180
	movdqu XMMWORD PTR [edi+112], xmm4
	pshufd xmm4, xmm6, 57
	pxor xmm1, xmm0
	pxor xmm6, xmm4
	pshufhw xmm3, xmm3, 180
	movdqu xmm0, XMMWORD PTR [eax+96]
	pxor xmm5, xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pshuflw xmm0, xmm0, 180
	pxor xmm1, xmm6
	pshufd xmm6, xmm6, 78
	movdqu XMMWORD PTR [edi+96], xmm5
	pshufd xmm5, xmm7, 57
	pxor xmm7, xmm5
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	pshufd xmm7, xmm7, 78
	pxor xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [eax+80]
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edi]
	pshuflw xmm6, xmm6, 180
	movdqu XMMWORD PTR [edi+80], xmm1
	pshufd xmm1, xmm3, 57
	pxor xmm3, xmm1
	pxor xmm7, xmm5
	pshufd xmm5, xmm3, 78
	pshufhw xmm0, xmm0, 180
	pshufhw xmm6, xmm6, 180
	pxor xmm3, xmm7
	movdqu xmm7, XMMWORD PTR [eax+64]
	pxor xmm4, xmm7
	pshufd xmm7, xmm6, 57
	pxor xmm6, xmm7
	pxor xmm3, xmm2
	pxor xmm5, xmm1
	pshufd xmm1, xmm6, 78
	movdqu XMMWORD PTR [edi+64], xmm4
	pshufd xmm4, xmm0, 57
	pxor xmm0, xmm4
	pxor xmm5, xmm6
	pxor xmm1, xmm7
	pxor xmm1, xmm0
	pshufd xmm0, xmm0, 78
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [eax+48]
	pxor xmm3, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [eax+16]
	pxor xmm1, xmm4
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [eax]
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [eax+32]
	pxor xmm5, xmm2
	movdqa xmm2, xmm5
	add eax, 128
	test ecx, ecx
	jmp 28f
27:
28:
	jne 26b
	movdqu xmm4, XMMWORD PTR [edi+80]
	pxor xmm2, xmm4
	movdqa xmm5, xmm2
	pxor xmm5, xmm1
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm5
	pxor xmm3, xmm6
	movdqu xmm7, XMMWORD PTR [edi+112]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi], xmm6
	movdqa xmm6, xmm3
	pxor xmm6, xmm2
	pxor xmm0, xmm5
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [edi+16], xmm7
	movdqa xmm7, xmm6
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi+64]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+48], xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm6
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm6, xmm7
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+128], xmm0
	movdqu xmm0, XMMWORD PTR [edi+112]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+144], xmm4
	movdqa xmm4, xmm6
	pand xmm4, xmm7
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm1
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu xmm7, XMMWORD PTR [edi+16]
	pand xmm7, xmm1
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+192], xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm3
	movdqu XMMWORD PTR [edi+208], xmm3
	movdqa xmm3, xmm6
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm6, XMMWORD PTR [edi+128]
	pand xmm6, xmm3
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [edi+240], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pand xmm3, xmm5
	pxor xmm7, xmm6
	pxor xmm7, xmm4
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pand xmm2, xmm0
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+96]
	pxor xmm3, xmm0
	pxor xmm1, xmm2
	pxor xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [edi+144]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm2
	movdqu XMMWORD PTR [edi+256], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pand xmm0, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	movdqu XMMWORD PTR [edi+272], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pand xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [edi+96]
	pand xmm6, xmm2
	pxor xmm1, xmm6
	pxor xmm0, xmm4
	movdqa xmm4, xmm3
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm0, xmm6
	pxor xmm2, xmm5
	pxor xmm1, xmm2
	movdqa xmm2, xmm1
	pxor xmm2, xmm4
	pxor xmm4, xmm0
	movdqa xmm6, xmm7
	pxor xmm6, xmm0
	pand xmm2, xmm6
	pxor xmm2, xmm0
	pxor xmm3, xmm1
	pxor xmm7, xmm2
	movdqa xmm6, xmm4
	pxor xmm6, xmm2
	pand xmm6, xmm0
	pxor xmm7, xmm6
	pand xmm5, xmm2
	pxor xmm6, xmm4
	pand xmm4, xmm3
	pxor xmm4, xmm1
	movdqu xmm0, XMMWORD PTR [edi+16]
	pand xmm0, xmm4
	pand xmm6, xmm4
	pxor xmm6, xmm3
	movdqa xmm1, xmm4
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi]
	pand xmm3, xmm7
	movdqu XMMWORD PTR [edi], xmm2
	movdqu xmm2, XMMWORD PTR [edi+128]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+192]
	pand xmm0, xmm4
	pxor xmm4, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu xmm5, XMMWORD PTR [edi+240]
	pand xmm5, xmm6
	pxor xmm0, xmm3
	pxor xmm6, xmm7
	movdqu XMMWORD PTR [edi+128], xmm3
	movdqu xmm3, XMMWORD PTR [edi+176]
	pand xmm3, xmm4
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+80]
	pand xmm2, xmm1
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+80], xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pand xmm2, xmm1
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu xmm3, XMMWORD PTR [edi+272]
	pand xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [edi+224]
	pand xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pand xmm3, xmm1
	pxor xmm3, xmm5
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	pxor xmm2, xmm0
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edi+16]
	pxor xmm6, xmm2
	movdqu XMMWORD PTR [edi+176], xmm2
	movdqu xmm2, XMMWORD PTR [edi+256]
	pand xmm2, xmm7
	pxor xmm6, xmm2
	movdqu xmm2, XMMWORD PTR [edi]
	pxor xmm7, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm2, xmm5
	pxor xmm6, xmm2
	movdqu xmm5, XMMWORD PTR [edi+16]
	pxor xmm5, xmm3
	pxor xmm2, xmm4
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+144]
	pand xmm2, xmm7
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [edi+96]
	pand xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi+208]
	pand xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [edi+32]
	pxor xmm2, xmm1
	movdqu xmm4, XMMWORD PTR [edi+48]
	pxor xmm2, xmm4
	pxor xmm1, xmm5
	pxor xmm7, xmm2
	movdqu xmm2, XMMWORD PTR [edi+160]
	pxor xmm7, xmm2
	movdqu xmm4, XMMWORD PTR [edi+128]
	pxor xmm4, xmm1
	pxor xmm1, xmm3
	pxor xmm2, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [edi+80]
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+48], xmm7
	movdqu XMMWORD PTR [edi+64], xmm6
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu xmm7, XMMWORD PTR [edi+176]
	movdqu XMMWORD PTR [edi], xmm7
	mov eax, edi
	add eax, 288
	mov ecx, 252645135
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm1, XMMWORD PTR [edi+64]
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm6
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm0, XMMWORD PTR [edi+16]
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm6
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm1, XMMWORD PTR [edi+96]
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm6
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu xmm0, XMMWORD PTR [edi+48]
	movdqu xmm1, XMMWORD PTR [edi+112]
	pshuflw xmm0, xmm0, 180
	pshufhw xmm0, xmm0, 180
	pshuflw xmm1, xmm1, 180
	pshufhw xmm1, xmm1, 180
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm6
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu XMMWORD PTR [edi+112], xmm1
	mov ecx, 16711935
	movd xmm5, ecx
	pshufd xmm5, xmm5, 0
	mov ecx, 1431655765
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	mov ecx, 858993459
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm4, xmm2
	pand xmm4, xmm7
	pxor xmm2, xmm4
	psllq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm4, xmm3
	pand xmm4, xmm7
	pxor xmm3, xmm4
	psllq xmm4, 2
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm4, xmm1
	pand xmm4, xmm6
	pxor xmm1, xmm4
	psllq xmm4, 1
	pxor xmm0, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm5
	pxor xmm1, xmm4
	psllq xmm4, 8
	pxor xmm0, xmm4
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm4
	punpckhqdq xmm1, xmm4
	movdqa xmm4, xmm2
	punpcklwd xmm2, xmm3
	punpckhwd xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm4
	punpckhwd xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 8
	pxor xmm4, xmm3
	pand xmm4, xmm5
	pxor xmm3, xmm4
	psllq xmm4, 8
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklqdq xmm2, xmm4
	punpckhqdq xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [eax]
	pxor xmm0, xmm4
	pxor xmm1, xmm4
	pxor xmm2, xmm4
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+16], xmm1
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [edi+80]
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [edi+112]
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm4, xmm2
	pand xmm4, xmm7
	pxor xmm2, xmm4
	psllq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm4, xmm3
	pand xmm4, xmm7
	pxor xmm3, xmm4
	psllq xmm4, 2
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm4, xmm1
	pand xmm4, xmm6
	pxor xmm1, xmm4
	psllq xmm4, 1
	pxor xmm0, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqa xmm4, xmm0
	psrlq xmm4, 8
	pxor xmm4, xmm1
	pand xmm4, xmm5
	pxor xmm1, xmm4
	psllq xmm4, 8
	pxor xmm0, xmm4
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm4
	punpckhqdq xmm1, xmm4
	movdqa xmm4, xmm2
	punpcklwd xmm2, xmm3
	punpckhwd xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm4
	punpckhwd xmm3, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 8
	pxor xmm4, xmm3
	pand xmm4, xmm5
	pxor xmm3, xmm4
	psllq xmm4, 8
	pxor xmm2, xmm4
	movdqa xmm4, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm4, xmm3
	movdqa xmm3, xmm2
	punpcklqdq xmm2, xmm4
	punpckhqdq xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [eax]
	pxor xmm0, xmm4
	pxor xmm1, xmm4
	pxor xmm2, xmm4
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+112], xmm3
	mov esi, edi
	cmp ebp, 8
	jae 29f
	mov ecx, ebp
	jmp 210f
29:
	mov ecx, 8
210:
	sub ebp, ecx
211:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm1, XMMWORD PTR [edx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	add esi, 16
	add edx, 16
	add ebx, 16
	sub ecx, 1
	jne 211b
	test ebp, ebp
	jne 25b
	jmp 24f
23:
24:
	mov ebx, DWORD PTR [edi+304]
	mov esi, DWORD PTR [edi+308]
	mov ebp, DWORD PTR [edi+316]
	mov edi, DWORD PTR [edi+312]
	ret
	.p2align 6
