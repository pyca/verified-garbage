// The functions of `src/seed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	lea esp, [esp-764]
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+772]
	mov DWORD PTR [esp+8], eax
	mov eax, esp
	add eax, 16
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax+720], ebx
	mov DWORD PTR [eax+724], esi
	mov DWORD PTR [eax+728], edi
	mov DWORD PTR [eax+732], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	bswap eax
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [ecx+4]
	bswap eax
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [ecx+8]
	bswap eax
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [ecx+12]
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -1640531527
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -1640531527
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, 1013904243
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, 1013904243
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, 2027808486
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, 2027808486
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -239350324
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -239350324
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -478700647
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -478700647
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -957401293
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -957401293
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -1914802585
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -1914802585
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, 465362127
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, 465362127
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, 930724254
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, 930724254
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, 1861448508
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, 1861448508
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -572070280
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -572070280
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -1144140559
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -1144140559
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, 2006686179
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, 2006686179
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -281594938
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -281594938
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -563189875
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -563189875
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+704]
	ror eax, 8
	mov ebx, DWORD PTR [edi+708]
	ror ebx, 8
	mov ecx, eax
	xor ecx, ebx
	and ecx, -16777216
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+704], eax
	mov DWORD PTR [edi+708], ebx
	mov eax, DWORD PTR [edi+704]
	add eax, DWORD PTR [edi+712]
	sub eax, -1126379749
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [edi+708]
	sub eax, DWORD PTR [edi+716]
	add eax, -1126379749
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [edi+712]
	ror eax, 24
	mov ebx, DWORD PTR [edi+716]
	ror ebx, 24
	mov ecx, eax
	xor ecx, ebx
	and ecx, 255
	xor eax, ecx
	xor ebx, ecx
	mov DWORD PTR [edi+712], eax
	mov DWORD PTR [edi+716], ebx
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_SSE2}
	pop ecx
	movdqu xmm0, XMMWORD PTR [eax]
	mov ebx, eax
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu XMMWORD PTR [esi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [esi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [esi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu XMMWORD PTR [esi+64], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu XMMWORD PTR [esi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [esi+96], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [esi+112], xmm0
	mov ebx, DWORD PTR [edi+720]
	mov esi, DWORD PTR [edi+724]
	mov ebp, DWORD PTR [edi+732]
	mov edi, DWORD PTR [edi+728]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	lea esp, [esp+764]
	lea esp, [esp-768]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+756], ecx
	mov DWORD PTR [esp+760], ecx
	mov DWORD PTR [esp+764], ecx
	lea esp, [esp+768]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_seed_ecb_encrypt_aesni:
	lea esp, [esp-736]
	mov eax, DWORD PTR [esp+740]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+672], ebx
	mov DWORD PTR [eax+676], esi
	mov DWORD PTR [eax+680], edi
	mov DWORD PTR [eax+684], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+692]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+668], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
24:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+692]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
28:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 28b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+692]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
212:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 212b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [edi+672]
	mov esi, DWORD PTR [edi+676]
	mov ebp, DWORD PTR [edi+684]
	mov edi, DWORD PTR [edi+680]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	lea esp, [esp+736]
	lea esp, [esp-740]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+736], ecx
	lea esp, [esp+740]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_seed_ecb_encrypt:
	lea esp, [esp-1856]
	mov eax, DWORD PTR [esp+1860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1868]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+1792], ebx
	mov DWORD PTR [eax+1796], esi
	mov DWORD PTR [eax+1800], edi
	mov DWORD PTR [eax+1804], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_SSE2}
	pop ecx
	mov DWORD PTR [edi+480], eax
	movdqu xmm0, XMMWORD PTR [eax]
	mov eax, DWORD PTR [esp+4]
	add eax, 0
	mov esi, edi
	add esi, 1280
	mov ecx, 16
20:
	movq xmm0, QWORD PTR [eax]
	pshufd xmm1, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm1
	pshufd xmm1, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm1
	add eax, 8
	add esi, 32
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 16
	jb 21f
23:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+1276], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [esi+252], eax
	add esi, 256
	sub ebp, 16
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 16
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 8
	jb 24f
26:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1148], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 8
	jae 26b
	jmp 25f
24:
25:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 4
	jb 27f
29:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 4
	jae 29b
	jmp 28f
27:
28:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 2
	jb 210f
212:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 2
	jae 212b
	jmp 211f
210:
211:
	mov eax, DWORD PTR [edi+1812]
	test eax, eax
	je 213f
215:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	jne 215b
	jmp 214f
213:
214:
	mov ebx, DWORD PTR [edi+1792]
	mov esi, DWORD PTR [edi+1796]
	mov ebp, DWORD PTR [edi+1804]
	mov edi, DWORD PTR [edi+1800]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	movdqu XMMWORD PTR [esp+1108], xmm0
	movdqu XMMWORD PTR [esp+1124], xmm0
	movdqu XMMWORD PTR [esp+1140], xmm0
	movdqu XMMWORD PTR [esp+1156], xmm0
	movdqu XMMWORD PTR [esp+1172], xmm0
	movdqu XMMWORD PTR [esp+1188], xmm0
	movdqu XMMWORD PTR [esp+1204], xmm0
	movdqu XMMWORD PTR [esp+1220], xmm0
	movdqu XMMWORD PTR [esp+1236], xmm0
	movdqu XMMWORD PTR [esp+1252], xmm0
	movdqu XMMWORD PTR [esp+1268], xmm0
	movdqu XMMWORD PTR [esp+1284], xmm0
	movdqu XMMWORD PTR [esp+1300], xmm0
	movdqu XMMWORD PTR [esp+1316], xmm0
	movdqu XMMWORD PTR [esp+1332], xmm0
	movdqu XMMWORD PTR [esp+1348], xmm0
	movdqu XMMWORD PTR [esp+1364], xmm0
	movdqu XMMWORD PTR [esp+1380], xmm0
	movdqu XMMWORD PTR [esp+1396], xmm0
	movdqu XMMWORD PTR [esp+1412], xmm0
	movdqu XMMWORD PTR [esp+1428], xmm0
	movdqu XMMWORD PTR [esp+1444], xmm0
	movdqu XMMWORD PTR [esp+1460], xmm0
	movdqu XMMWORD PTR [esp+1476], xmm0
	movdqu XMMWORD PTR [esp+1492], xmm0
	movdqu XMMWORD PTR [esp+1508], xmm0
	movdqu XMMWORD PTR [esp+1524], xmm0
	movdqu XMMWORD PTR [esp+1540], xmm0
	movdqu XMMWORD PTR [esp+1556], xmm0
	movdqu XMMWORD PTR [esp+1572], xmm0
	movdqu XMMWORD PTR [esp+1588], xmm0
	movdqu XMMWORD PTR [esp+1604], xmm0
	movdqu XMMWORD PTR [esp+1620], xmm0
	movdqu XMMWORD PTR [esp+1636], xmm0
	movdqu XMMWORD PTR [esp+1652], xmm0
	movdqu XMMWORD PTR [esp+1668], xmm0
	movdqu XMMWORD PTR [esp+1684], xmm0
	movdqu XMMWORD PTR [esp+1700], xmm0
	movdqu XMMWORD PTR [esp+1716], xmm0
	movdqu XMMWORD PTR [esp+1732], xmm0
	movdqu XMMWORD PTR [esp+1748], xmm0
	movdqu XMMWORD PTR [esp+1764], xmm0
	movdqu XMMWORD PTR [esp+1780], xmm0
	movdqu XMMWORD PTR [esp+1796], xmm0
	movdqu XMMWORD PTR [esp+1812], xmm0
	movdqu XMMWORD PTR [esp+1828], xmm0
	mov DWORD PTR [esp+1844], ecx
	mov DWORD PTR [esp+1848], ecx
	lea esp, [esp+1856]
	lea esp, [esp-1864]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+1860], ecx
	lea esp, [esp+1864]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_seed_ecb_decrypt_aesni:
	lea esp, [esp-736]
	mov eax, DWORD PTR [esp+740]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+672], ebx
	mov DWORD PTR [eax+676], esi
	mov DWORD PTR [eax+680], edi
	mov DWORD PTR [eax+684], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 544
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	sub esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [edi+692]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+668], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
24:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+692]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
28:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 28b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+692]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
212:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 212b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	jne 211b
	jmp 210f
29:
210:
	mov ebx, DWORD PTR [edi+672]
	mov esi, DWORD PTR [edi+676]
	mov ebp, DWORD PTR [edi+684]
	mov edi, DWORD PTR [edi+680]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	lea esp, [esp+736]
	lea esp, [esp-740]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+736], ecx
	lea esp, [esp+740]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_seed_ecb_decrypt:
	lea esp, [esp-1856]
	mov eax, DWORD PTR [esp+1860]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1864]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1868]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+1792], ebx
	mov DWORD PTR [eax+1796], esi
	mov DWORD PTR [eax+1800], edi
	mov DWORD PTR [eax+1804], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_SSE2}
	pop ecx
	mov DWORD PTR [edi+480], eax
	movdqu xmm0, XMMWORD PTR [eax]
	mov eax, DWORD PTR [esp+4]
	add eax, 120
	mov esi, edi
	add esi, 1280
	mov ecx, 16
20:
	movq xmm0, QWORD PTR [eax]
	pshufd xmm1, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm1
	pshufd xmm1, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm1
	sub eax, 8
	add esi, 32
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 16
	jb 21f
23:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+1276], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [esi+252], eax
	add esi, 256
	sub ebp, 16
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 16
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 8
	jb 24f
26:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1148], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 8
	jae 26b
	jmp 25f
24:
25:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 4
	jb 27f
29:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 4
	jae 29b
	jmp 28f
27:
28:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 2
	jb 210f
212:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 2
	jae 212b
	jmp 211f
210:
211:
	mov eax, DWORD PTR [edi+1812]
	test eax, eax
	je 213f
215:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	jne 215b
	jmp 214f
213:
214:
	mov ebx, DWORD PTR [edi+1792]
	mov esi, DWORD PTR [edi+1796]
	mov ebp, DWORD PTR [edi+1804]
	mov edi, DWORD PTR [edi+1800]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	movdqu XMMWORD PTR [esp+1108], xmm0
	movdqu XMMWORD PTR [esp+1124], xmm0
	movdqu XMMWORD PTR [esp+1140], xmm0
	movdqu XMMWORD PTR [esp+1156], xmm0
	movdqu XMMWORD PTR [esp+1172], xmm0
	movdqu XMMWORD PTR [esp+1188], xmm0
	movdqu XMMWORD PTR [esp+1204], xmm0
	movdqu XMMWORD PTR [esp+1220], xmm0
	movdqu XMMWORD PTR [esp+1236], xmm0
	movdqu XMMWORD PTR [esp+1252], xmm0
	movdqu XMMWORD PTR [esp+1268], xmm0
	movdqu XMMWORD PTR [esp+1284], xmm0
	movdqu XMMWORD PTR [esp+1300], xmm0
	movdqu XMMWORD PTR [esp+1316], xmm0
	movdqu XMMWORD PTR [esp+1332], xmm0
	movdqu XMMWORD PTR [esp+1348], xmm0
	movdqu XMMWORD PTR [esp+1364], xmm0
	movdqu XMMWORD PTR [esp+1380], xmm0
	movdqu XMMWORD PTR [esp+1396], xmm0
	movdqu XMMWORD PTR [esp+1412], xmm0
	movdqu XMMWORD PTR [esp+1428], xmm0
	movdqu XMMWORD PTR [esp+1444], xmm0
	movdqu XMMWORD PTR [esp+1460], xmm0
	movdqu XMMWORD PTR [esp+1476], xmm0
	movdqu XMMWORD PTR [esp+1492], xmm0
	movdqu XMMWORD PTR [esp+1508], xmm0
	movdqu XMMWORD PTR [esp+1524], xmm0
	movdqu XMMWORD PTR [esp+1540], xmm0
	movdqu XMMWORD PTR [esp+1556], xmm0
	movdqu XMMWORD PTR [esp+1572], xmm0
	movdqu XMMWORD PTR [esp+1588], xmm0
	movdqu XMMWORD PTR [esp+1604], xmm0
	movdqu XMMWORD PTR [esp+1620], xmm0
	movdqu XMMWORD PTR [esp+1636], xmm0
	movdqu XMMWORD PTR [esp+1652], xmm0
	movdqu XMMWORD PTR [esp+1668], xmm0
	movdqu XMMWORD PTR [esp+1684], xmm0
	movdqu XMMWORD PTR [esp+1700], xmm0
	movdqu XMMWORD PTR [esp+1716], xmm0
	movdqu XMMWORD PTR [esp+1732], xmm0
	movdqu XMMWORD PTR [esp+1748], xmm0
	movdqu XMMWORD PTR [esp+1764], xmm0
	movdqu XMMWORD PTR [esp+1780], xmm0
	movdqu XMMWORD PTR [esp+1796], xmm0
	movdqu XMMWORD PTR [esp+1812], xmm0
	movdqu XMMWORD PTR [esp+1828], xmm0
	mov DWORD PTR [esp+1844], ecx
	mov DWORD PTR [esp+1848], ecx
	lea esp, [esp+1856]
	lea esp, [esp-1864]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+1860], ecx
	lea esp, [esp+1864]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
