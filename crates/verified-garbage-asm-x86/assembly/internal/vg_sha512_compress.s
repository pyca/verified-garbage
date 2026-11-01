// The functions of `src/internal/vg_sha512_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+200], ebx
	mov DWORD PTR [eax+204], esi
	mov DWORD PTR [eax+208], edi
	mov DWORD PTR [eax+212], ebp
	mov esi, eax
	mov edi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [esi+216], eax
	test eax, eax
	je 20f
22:
	mov ecx, DWORD PTR [esp+4]
	movq xmm6, QWORD PTR [ecx]
	movq QWORD PTR [esi], xmm6
	movq xmm6, QWORD PTR [ecx+8]
	movq QWORD PTR [esi+8], xmm6
	movq xmm6, QWORD PTR [ecx+16]
	movq QWORD PTR [esi+16], xmm6
	movq xmm6, QWORD PTR [ecx+24]
	movq QWORD PTR [esi+24], xmm6
	movq xmm6, QWORD PTR [ecx+32]
	movq QWORD PTR [esi+32], xmm6
	movq xmm6, QWORD PTR [ecx+40]
	movq QWORD PTR [esi+40], xmm6
	movq xmm6, QWORD PTR [ecx+48]
	movq QWORD PTR [esi+48], xmm6
	movq xmm6, QWORD PTR [ecx+56]
	movq QWORD PTR [esi+56], xmm6
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+64], ecx
	mov DWORD PTR [esi+68], edx
	mov ecx, DWORD PTR [edi+12]
	mov edx, DWORD PTR [edi+8]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+72], ecx
	mov DWORD PTR [esi+76], edx
	mov ecx, DWORD PTR [edi+20]
	mov edx, DWORD PTR [edi+16]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+80], ecx
	mov DWORD PTR [esi+84], edx
	mov ecx, DWORD PTR [edi+28]
	mov edx, DWORD PTR [edi+24]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+88], ecx
	mov DWORD PTR [esi+92], edx
	mov ecx, DWORD PTR [edi+36]
	mov edx, DWORD PTR [edi+32]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+96], ecx
	mov DWORD PTR [esi+100], edx
	mov ecx, DWORD PTR [edi+44]
	mov edx, DWORD PTR [edi+40]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+104], ecx
	mov DWORD PTR [esi+108], edx
	mov ecx, DWORD PTR [edi+52]
	mov edx, DWORD PTR [edi+48]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+112], ecx
	mov DWORD PTR [esi+116], edx
	mov ecx, DWORD PTR [edi+60]
	mov edx, DWORD PTR [edi+56]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+120], ecx
	mov DWORD PTR [esi+124], edx
	mov ecx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+64]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+128], ecx
	mov DWORD PTR [esi+132], edx
	mov ecx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+72]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+136], ecx
	mov DWORD PTR [esi+140], edx
	mov ecx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+80]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+144], ecx
	mov DWORD PTR [esi+148], edx
	mov ecx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+88]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+152], ecx
	mov DWORD PTR [esi+156], edx
	mov ecx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+96]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+160], ecx
	mov DWORD PTR [esi+164], edx
	mov ecx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+104]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+168], ecx
	mov DWORD PTR [esi+172], edx
	mov ecx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+112]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+176], ecx
	mov DWORD PTR [esi+180], edx
	mov ecx, DWORD PTR [edi+124]
	mov edx, DWORD PTR [edi+120]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+184], ecx
	mov DWORD PTR [esi+188], edx
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi]
	bswap ecx
	bswap edx
	mov DWORD PTR [esi+192], ecx
	mov DWORD PTR [esi+196], edx
	movq xmm0, QWORD PTR [esi]
	movq xmm1, QWORD PTR [esi+32]
	movq xmm2, QWORD PTR [esi+8]
	movq xmm6, QWORD PTR [esi+16]
	pxor xmm2, xmm6
	movq xmm3, QWORD PTR [esi+56]
	mov eax, -685199838
	movd xmm6, eax
	mov eax, 1116352408
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+64]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 602891725
	movd xmm6, eax
	mov eax, 1899447441
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+72]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -330482897
	movd xmm6, eax
	mov eax, -1245643825
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+80]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -2121671748
	movd xmm6, eax
	mov eax, -373957723
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+88]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+24]
	mov eax, -213338824
	movd xmm6, eax
	mov eax, 961987163
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+96]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, -1241133031
	movd xmm6, eax
	mov eax, 1508970993
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+104]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+8]
	mov eax, -1357295717
	movd xmm6, eax
	mov eax, -1841331548
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+112]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, -630357736
	movd xmm6, eax
	mov eax, -1424204075
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+120]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+56]
	mov eax, -1560083902
	movd xmm6, eax
	mov eax, -670586216
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+128]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 1164996542
	movd xmm6, eax
	mov eax, 310598401
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+136]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+40]
	mov eax, 1323610764
	movd xmm6, eax
	mov eax, 607225278
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+144]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -704662302
	movd xmm6, eax
	mov eax, 1426881987
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+152]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+24]
	mov eax, -226784913
	movd xmm6, eax
	mov eax, 1925078388
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+160]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, 991336113
	movd xmm6, eax
	mov eax, -2132889090
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+168]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq xmm3, QWORD PTR [esi+8]
	mov eax, 633803317
	movd xmm6, eax
	mov eax, -1680079193
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+176]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, -815192428
	movd xmm6, eax
	mov eax, -1046744716
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+184]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+176]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+64]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+64], xmm3
	movq QWORD PTR [esi+192], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, -1628353838
	movd xmm6, eax
	mov eax, -459576895
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+64]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 944711139
	movd xmm6, eax
	mov eax, -272742522
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+72]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+64]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+80]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+80], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -1953704523
	movd xmm6, eax
	mov eax, 264347078
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+80]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, 2007800933
	movd xmm6, eax
	mov eax, 604807628
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+88]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+80]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+96]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+96], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, 1495990901
	movd xmm6, eax
	mov eax, 770255983
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+96]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, 1856431235
	movd xmm6, eax
	mov eax, 1249150122
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+104]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+96]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+112]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+112], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, -1119749164
	movd xmm6, eax
	mov eax, 1555081692
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+112]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, -2096016459
	movd xmm6, eax
	mov eax, 1996064986
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+120]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+112]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+128]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+128], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, -295247957
	movd xmm6, eax
	mov eax, -1740746414
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+128]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 766784016
	movd xmm6, eax
	mov eax, -1473132947
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+136]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+128]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+144]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+144], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -1728372417
	movd xmm6, eax
	mov eax, -1341970488
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+144]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -1091629340
	movd xmm6, eax
	mov eax, -1084653625
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+152]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+144]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+160]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+160], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, 1034457026
	movd xmm6, eax
	mov eax, -958395405
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+160]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, -1828018395
	movd xmm6, eax
	mov eax, -710438585
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+168]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+160]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+176]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+176], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, -536640913
	movd xmm6, eax
	mov eax, 113926993
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+176]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, 168717936
	movd xmm6, eax
	mov eax, 338241895
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+184]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+176]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+64]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+64], xmm3
	movq QWORD PTR [esi+192], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, 1188179964
	movd xmm6, eax
	mov eax, 666307205
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+64]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 1546045734
	movd xmm6, eax
	mov eax, 773529912
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+72]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+64]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+80]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+80], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, 1522805485
	movd xmm6, eax
	mov eax, 1294757372
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+80]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -1651133473
	movd xmm6, eax
	mov eax, 1396182291
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+88]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+80]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+96]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+96], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, -1951439906
	movd xmm6, eax
	mov eax, 1695183700
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+96]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, 1014477480
	movd xmm6, eax
	mov eax, 1986661051
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+104]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+96]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+112]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+112], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, 1206759142
	movd xmm6, eax
	mov eax, -2117940946
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+112]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, 344077627
	movd xmm6, eax
	mov eax, -1838011259
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+120]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+112]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+128]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+128], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, 1290863460
	movd xmm6, eax
	mov eax, -1564481375
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+128]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, -1136513023
	movd xmm6, eax
	mov eax, -1474664885
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+136]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+128]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+144]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+144], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -789014639
	movd xmm6, eax
	mov eax, -1035236496
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+144]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, 106217008
	movd xmm6, eax
	mov eax, -949202525
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+152]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+144]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+160]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+160], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, -688958952
	movd xmm6, eax
	mov eax, -778901479
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+160]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, 1432725776
	movd xmm6, eax
	mov eax, -694614492
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+168]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+160]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+176]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+176], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, 1467031594
	movd xmm6, eax
	mov eax, -200395387
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+176]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, 851169720
	movd xmm6, eax
	mov eax, 275423344
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+184]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+176]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+64]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+64], xmm3
	movq QWORD PTR [esi+192], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, -1194143544
	movd xmm6, eax
	mov eax, 430227734
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+64]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 1363258195
	movd xmm6, eax
	mov eax, 506948616
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+72]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+64]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+80]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+80], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -544281703
	movd xmm6, eax
	mov eax, 659060556
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+80]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -509917016
	movd xmm6, eax
	mov eax, 883997877
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+88]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+80]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+96]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+96], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, -976659869
	movd xmm6, eax
	mov eax, 958139571
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+96]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, -482243893
	movd xmm6, eax
	mov eax, 1322822218
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+104]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+96]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+112]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+112], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, 2003034995
	movd xmm6, eax
	mov eax, 1537002063
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+112]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, -692930397
	movd xmm6, eax
	mov eax, 1747873779
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+120]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+112]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+128]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+128], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, 1575990012
	movd xmm6, eax
	mov eax, 1955562222
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+128]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 1125592928
	movd xmm6, eax
	mov eax, 2024104815
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+136]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+128]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+144]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+144], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -1578062990
	movd xmm6, eax
	mov eax, -2067236844
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+144]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, 442776044
	movd xmm6, eax
	mov eax, -1933114872
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+152]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+144]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+160]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+160], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, 593698344
	movd xmm6, eax
	mov eax, -1866530822
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+160]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, -561857047
	movd xmm6, eax
	mov eax, -1538233109
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+168]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+160]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+176]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+176], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, -1295615723
	movd xmm6, eax
	mov eax, -1090935817
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+176]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, -479046869
	movd xmm6, eax
	mov eax, -965641998
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+184]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+176]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+64]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+64], xmm3
	movq QWORD PTR [esi+192], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, -366583396
	movd xmm6, eax
	mov eax, -903397682
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+64]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 566280711
	movd xmm6, eax
	mov eax, -779700025
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+72]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+64]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+80]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+80], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, -840897762
	movd xmm6, eax
	mov eax, -354779690
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+80]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -294727304
	movd xmm6, eax
	mov eax, -176337025
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+88]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+80]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+96]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+96], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, 1914138554
	movd xmm6, eax
	mov eax, 116418474
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+96]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, -1563912026
	movd xmm6, eax
	mov eax, 174292421
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+104]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+96]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+112]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+112], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, -1090974290
	movd xmm6, eax
	mov eax, 289380356
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+112]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, 320620315
	movd xmm6, eax
	mov eax, 460393269
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+120]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+112]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+72]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+136]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+128]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+128], xmm3
	movq xmm3, QWORD PTR [esi+56]
	mov eax, 587496836
	movd xmm6, eax
	mov eax, 685471733
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+128]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [esi+48]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+32], xmm1
	movq xmm4, QWORD PTR [esi+24]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+8]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+48]
	mov eax, 1086792851
	movd xmm6, eax
	mov eax, 852142971
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+136]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [esi+40]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+24], xmm4
	movq xmm1, QWORD PTR [esi+16]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+56], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+128]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+88]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+152]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+144]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+144], xmm3
	movq xmm3, QWORD PTR [esi+40]
	mov eax, 365543100
	movd xmm6, eax
	mov eax, 1017036298
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+144]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [esi+32]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+16], xmm1
	movq xmm4, QWORD PTR [esi+8]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+56]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+48], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+32]
	mov eax, -1676669620
	movd xmm6, eax
	mov eax, 1126000580
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+152]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [esi+24]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+8], xmm4
	movq xmm1, QWORD PTR [esi]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+48]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+40], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+144]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+104]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+168]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+160]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+160], xmm3
	movq xmm3, QWORD PTR [esi+24]
	mov eax, -885112138
	movd xmm6, eax
	mov eax, 1288033470
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+160]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [esi+16]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi], xmm1
	movq xmm4, QWORD PTR [esi+56]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+40]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+32], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi+16]
	mov eax, -60457430
	movd xmm6, eax
	mov eax, 1501505948
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+168]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [esi+8]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+56], xmm4
	movq xmm1, QWORD PTR [esi+48]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+32]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+24], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [esi+160]
	movdqa xmm7, xmm6
	psrlq xmm6, 6
	psllq xmm7, 3
	movdqa xmm3, xmm6
	pxor xmm3, xmm7
	psrlq xmm6, 13
	pxor xmm3, xmm6
	psllq xmm7, 42
	pxor xmm3, xmm7
	psrlq xmm6, 42
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+120]
	paddq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+184]
	movdqa xmm7, xmm6
	psrlq xmm6, 1
	psllq xmm7, 56
	movdqa xmm4, xmm6
	pxor xmm4, xmm7
	psrlq xmm6, 6
	pxor xmm4, xmm6
	psllq xmm7, 7
	pxor xmm4, xmm7
	psrlq xmm6, 1
	pxor xmm4, xmm6
	paddq xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [esi+176]
	paddq xmm3, xmm6
	movdqu XMMWORD PTR [esi+176], xmm3
	movq xmm3, QWORD PTR [esi+8]
	mov eax, 987167468
	movd xmm6, eax
	mov eax, 1607167915
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+176]
	paddq xmm3, xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [esi]
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm7
	paddq xmm3, xmm6
	movq QWORD PTR [esi+48], xmm1
	movq xmm4, QWORD PTR [esi+40]
	paddq xmm4, xmm3
	movdqa xmm6, xmm1
	psrlq xmm6, 14
	movdqa xmm5, xmm6
	psrlq xmm6, 4
	pxor xmm5, xmm6
	psrlq xmm6, 23
	pxor xmm5, xmm6
	psllq xmm1, 23
	movdqa xmm7, xmm1
	psllq xmm1, 23
	pxor xmm7, xmm1
	psllq xmm1, 4
	pxor xmm7, xmm1
	pxor xmm5, xmm7
	paddq xmm3, xmm5
	paddq xmm4, xmm5
	movq xmm6, QWORD PTR [esi+24]
	movdqa xmm5, xmm0
	pxor xmm5, xmm6
	pand xmm2, xmm5
	pxor xmm2, xmm6
	paddq xmm3, xmm2
	movq QWORD PTR [esi+16], xmm0
	movdqa xmm6, xmm0
	psrlq xmm6, 28
	movdqa xmm2, xmm6
	psrlq xmm6, 6
	pxor xmm2, xmm6
	psrlq xmm6, 5
	pxor xmm2, xmm6
	psllq xmm0, 25
	movdqa xmm7, xmm0
	psllq xmm0, 5
	pxor xmm7, xmm0
	psllq xmm0, 6
	pxor xmm7, xmm0
	pxor xmm2, xmm7
	paddq xmm3, xmm2
	movq xmm0, QWORD PTR [esi]
	mov eax, 1246189591
	movd xmm6, eax
	mov eax, 1816402316
	movd xmm7, eax
	punpckldq xmm6, xmm7
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+184]
	paddq xmm0, xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [esi+56]
	pxor xmm6, xmm7
	pand xmm6, xmm4
	pxor xmm6, xmm7
	paddq xmm0, xmm6
	movq QWORD PTR [esi+40], xmm4
	movq xmm1, QWORD PTR [esi+32]
	paddq xmm1, xmm0
	movdqa xmm6, xmm4
	psrlq xmm6, 14
	movdqa xmm2, xmm6
	psrlq xmm6, 4
	pxor xmm2, xmm6
	psrlq xmm6, 23
	pxor xmm2, xmm6
	psllq xmm4, 23
	movdqa xmm7, xmm4
	psllq xmm4, 23
	pxor xmm7, xmm4
	psllq xmm4, 4
	pxor xmm7, xmm4
	pxor xmm2, xmm7
	paddq xmm0, xmm2
	paddq xmm1, xmm2
	movq xmm6, QWORD PTR [esi+16]
	movdqa xmm2, xmm3
	pxor xmm2, xmm6
	pand xmm5, xmm2
	pxor xmm5, xmm6
	paddq xmm0, xmm5
	movq QWORD PTR [esi+8], xmm3
	movdqa xmm6, xmm3
	psrlq xmm6, 28
	movdqa xmm5, xmm6
	psrlq xmm6, 6
	pxor xmm5, xmm6
	psrlq xmm6, 5
	pxor xmm5, xmm6
	psllq xmm3, 25
	movdqa xmm7, xmm3
	psllq xmm3, 5
	pxor xmm7, xmm3
	psllq xmm3, 6
	pxor xmm7, xmm3
	pxor xmm5, xmm7
	paddq xmm0, xmm5
	movq QWORD PTR [esi], xmm0
	movq QWORD PTR [esi+32], xmm1
	mov ecx, DWORD PTR [esp+4]
	movq xmm6, QWORD PTR [esi]
	movq xmm7, QWORD PTR [ecx]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx], xmm6
	movq xmm6, QWORD PTR [esi+8]
	movq xmm7, QWORD PTR [ecx+8]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+8], xmm6
	movq xmm6, QWORD PTR [esi+16]
	movq xmm7, QWORD PTR [ecx+16]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+16], xmm6
	movq xmm6, QWORD PTR [esi+24]
	movq xmm7, QWORD PTR [ecx+24]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+24], xmm6
	movq xmm6, QWORD PTR [esi+32]
	movq xmm7, QWORD PTR [ecx+32]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+32], xmm6
	movq xmm6, QWORD PTR [esi+40]
	movq xmm7, QWORD PTR [ecx+40]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+40], xmm6
	movq xmm6, QWORD PTR [esi+48]
	movq xmm7, QWORD PTR [ecx+48]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+48], xmm6
	movq xmm6, QWORD PTR [esi+56]
	movq xmm7, QWORD PTR [ecx+56]
	paddq xmm6, xmm7
	movq QWORD PTR [ecx+56], xmm6
	add edi, 128
	mov eax, DWORD PTR [esi+216]
	sub eax, 1
	mov DWORD PTR [esi+216], eax
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esi+200]
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	mov esi, DWORD PTR [esi+204]
	ret
	.p2align 6
