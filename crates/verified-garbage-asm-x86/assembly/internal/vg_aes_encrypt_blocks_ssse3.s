// The functions of `src/internal/vg_aes_encrypt_blocks_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_encrypt_blocks_ssse3:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+464], ebx
	mov DWORD PTR [eax+468], esi
	mov DWORD PTR [eax+472], ebp
	mov DWORD PTR [eax+476], edi
	mov edi, eax
	mov eax, 909574400
	mov DWORD PTR [edi], eax
	mov eax, -421015088
	mov DWORD PTR [edi+4], eax
	mov eax, -454700078
	mov DWORD PTR [edi+8], eax
	mov eax, 875889410
	mov DWORD PTR [edi+12], eax
	mov eax, 847858162
	mov DWORD PTR [edi+16], eax
	mov eax, -1925777843
	mov DWORD PTR [edi+20], eax
	mov eax, -96370374
	mov DWORD PTR [edi+24], eax
	mov eax, 1174290053
	mov DWORD PTR [edi+28], eax
	mov eax, 218628480
	mov DWORD PTR [edi+32], eax
	mov eax, 235210255
	mov DWORD PTR [edi+36], eax
	mov eax, 168496130
	mov DWORD PTR [edi+40], eax
	mov eax, 67568393
	mov DWORD PTR [edi+44], eax
	mov eax, 201392768
	mov DWORD PTR [edi+48], eax
	mov eax, 168626952
	mov DWORD PTR [edi+52], eax
	mov eax, 84348420
	mov DWORD PTR [edi+56], eax
	mov eax, 252249603
	mov DWORD PTR [edi+60], eax
	mov eax, 252314880
	mov DWORD PTR [edi+64], eax
	mov eax, 51251460
	mov DWORD PTR [edi+68], eax
	mov eax, 117574920
	mov DWORD PTR [edi+72], eax
	mov eax, 184942860
	mov DWORD PTR [edi+76], eax
	mov eax, 197121
	mov DWORD PTR [edi+80], eax
	mov eax, 67569157
	mov DWORD PTR [edi+84], eax
	mov eax, 134941193
	mov DWORD PTR [edi+88], eax
	mov eax, 202313229
	mov DWORD PTR [edi+92], eax
	mov eax, 287396352
	mov DWORD PTR [edi+96], eax
	mov eax, -1104109588
	mov DWORD PTR [edi+100], eax
	mov eax, -594656259
	mov DWORD PTR [edi+104], eax
	mov eax, 1657646963
	mov DWORD PTR [edi+108], eax
	mov eax, -1600599808
	mov DWORD PTR [edi+112], eax
	mov eax, 2100880820
	mov DWORD PTR [edi+116], eax
	mov eax, -1941608172
	mov DWORD PTR [edi+120], eax
	mov eax, -248717999
	mov DWORD PTR [edi+124], eax
	mov eax, 555497472
	mov DWORD PTR [edi+128], eax
	mov eax, -12721209
	mov DWORD PTR [edi+132], eax
	mov eax, -87942682
	mov DWORD PTR [edi+136], eax
	mov eax, 98295332
	mov DWORD PTR [edi+140], eax
	mov eax, -1475450880
	mov DWORD PTR [edi+144], eax
	mov eax, 1705405197
	mov DWORD PTR [edi+148], eax
	mov eax, -1413234523
	mov DWORD PTR [edi+152], eax
	mov eax, -838611610
	mov DWORD PTR [edi+156], eax
	mov eax, 896203264
	mov DWORD PTR [edi+160], eax
	mov eax, 1096756155
	mov DWORD PTR [edi+164], eax
	mov eax, -467742834
	mov DWORD PTR [edi+168], eax
	mov eax, -1512999792
	mov DWORD PTR [edi+172], eax
	mov eax, -1720286976
	mov DWORD PTR [edi+176], eax
	mov eax, 2096040701
	mov DWORD PTR [edi+180], eax
	mov eax, 311629924
	mov DWORD PTR [edi+184], eax
	mov eax, 1854662135
	mov DWORD PTR [edi+188], eax
	mov eax, 252645135
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+192], xmm0
	pshufb xmm0, xmm1
	pshufb xmm0, xmm1
	movdqu XMMWORD PTR [edi+208], xmm0
	movdqu xmm6, XMMWORD PTR [edi+32]
	mov esi, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, edi
	add ebx, 224
20:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi]
	pshufb xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [edi+16]
	pshufb xmm0, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [ebx], xmm0
	add esi, 16
	add ebx, 16
	sub ecx, 1
	jne 20b
	mov eax, 1667457891
	movd xmm1, eax
	pshufd xmm1, xmm1, 0
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ebx], xmm0
	mov esi, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+16]
	test ebp, ebp
	je 21f
23:
	movdqu xmm0, XMMWORD PTR [esi]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi]
	pshufb xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [edi+16]
	pshufb xmm0, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+224]
	pxor xmm0, xmm1
	mov ebx, edi
	add ebx, 240
	mov ecx, DWORD PTR [esp+8]
	sub ecx, 1
24:
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+48]
	pshufb xmm2, xmm0
	pxor xmm0, xmm1
	movdqa xmm3, xmm6
	pshufb xmm3, xmm1
	movdqa xmm4, xmm6
	pshufb xmm4, xmm0
	pxor xmm3, xmm2
	pxor xmm4, xmm2
	movdqa xmm2, xmm6
	pshufb xmm2, xmm3
	movdqa xmm5, xmm6
	pshufb xmm5, xmm4
	pxor xmm2, xmm0
	pxor xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+96]
	pshufb xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+112]
	pshufb xmm1, xmm5
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+128]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [edi+144]
	pshufb xmm4, xmm5
	pxor xmm3, xmm4
	movdqu xmm1, XMMWORD PTR [edi+64]
	pshufb xmm3, xmm1
	movdqa xmm4, xmm0
	movdqu xmm1, XMMWORD PTR [edi+192]
	pshufb xmm4, xmm1
	movdqu xmm1, XMMWORD PTR [edi+208]
	pshufb xmm0, xmm1
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx]
	pxor xmm0, xmm2
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+80]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	add ebx, 16
	sub ecx, 1
	jne 24b
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [edi+48]
	pshufb xmm2, xmm0
	pxor xmm0, xmm1
	movdqa xmm3, xmm6
	pshufb xmm3, xmm1
	movdqa xmm4, xmm6
	pshufb xmm4, xmm0
	pxor xmm3, xmm2
	pxor xmm4, xmm2
	movdqa xmm2, xmm6
	pshufb xmm2, xmm3
	movdqa xmm5, xmm6
	pshufb xmm5, xmm4
	pxor xmm2, xmm0
	pxor xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+160]
	pshufb xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+176]
	pshufb xmm1, xmm5
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pshufb xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub ebp, 1
	jne 23b
	jmp 22f
21:
22:
	mov ebx, DWORD PTR [edi+464]
	mov esi, DWORD PTR [edi+468]
	mov ebp, DWORD PTR [edi+472]
	mov edi, DWORD PTR [edi+476]
	ret
	.p2align 6
