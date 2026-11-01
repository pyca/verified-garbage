// The functions of `src/cast5_cfb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_cfb64_encrypt:
	lea esp, [esp-332]
	mov eax, DWORD PTR [esp+336]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+340]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+344]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+348]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+352]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+264], ebx
	mov DWORD PTR [eax+268], esi
	mov DWORD PTR [eax+272], edi
	mov DWORD PTR [eax+276], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+284], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+260], eax
	mov esi, edi
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+52], eax
	mov eax, esi
	add eax, 256
	mov DWORD PTR [esi+56], eax
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
	mov eax, DWORD PTR [esi+280]
	mov ecx, DWORD PTR [esi+284]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+280], eax
	mov DWORD PTR [esi+284], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+280], esi
	mov DWORD PTR [edi+284], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+264]
	mov esi, DWORD PTR [edi+268]
	mov ebp, DWORD PTR [edi+276]
	mov edi, DWORD PTR [edi+272]
	mov ecx, 0
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	lea esp, [esp+332]
	ret
	.p2align 6

vg_cast5_cfb64_decrypt:
	lea esp, [esp-332]
	mov eax, DWORD PTR [esp+336]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+340]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+344]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+348]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+352]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+264], ebx
	mov DWORD PTR [eax+268], esi
	mov DWORD PTR [eax+272], edi
	mov DWORD PTR [eax+276], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+280], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+284], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [edi+256], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [edi+260], eax
	mov esi, edi
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+52], eax
	mov eax, esi
	add eax, 256
	mov DWORD PTR [esi+56], eax
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
	mov eax, DWORD PTR [esi+280]
	mov ecx, DWORD PTR [esi+284]
	bswap ebp
	mov DWORD PTR [edx], ebp
	bswap ebx
	mov DWORD PTR [edx+4], ebx
	mov DWORD PTR [esi+280], eax
	mov DWORD PTR [esi+284], ecx
	mov edi, esi
	mov esi, DWORD PTR [edi+280]
	mov ebp, DWORD PTR [edi+284]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+256]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+260]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+280], esi
	mov DWORD PTR [edi+284], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+288]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+292]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+264]
	mov esi, DWORD PTR [edi+268]
	mov ebp, DWORD PTR [edi+276]
	mov edi, DWORD PTR [edi+272]
	mov ecx, 0
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	lea esp, [esp+332]
	ret
	.p2align 6
