// The functions of `src/internal/vg_camellia_ctr_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr_core:
	lea esp, [esp-1572]
	mov eax, DWORD PTR [esp+1576]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1592]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_SSE2}
	pop ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, edi
	add esi, 960
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm6, XMMWORD PTR [ebx+128]
	cmp ecx, 18
	je 20f
	mov ecx, 34
	jmp 21f
20:
	mov ecx, 26
21:
22:
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	add eax, 8
	sub ecx, 1
	jne 22b
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1524], eax
	test eax, eax
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 16
	jb 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [esi+128]
	xor eax, DWORD PTR [edi+832]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [esi+132]
	xor eax, DWORD PTR [edi+836]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [esi+136]
	xor eax, DWORD PTR [edi+840]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [esi+140]
	xor eax, DWORD PTR [edi+844]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [esi+144]
	xor eax, DWORD PTR [edi+848]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [esi+148]
	xor eax, DWORD PTR [edi+852]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [esi+152]
	xor eax, DWORD PTR [edi+856]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [esi+156]
	xor eax, DWORD PTR [edi+860]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [esi+160]
	xor eax, DWORD PTR [edi+864]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [esi+164]
	xor eax, DWORD PTR [edi+868]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [esi+168]
	xor eax, DWORD PTR [edi+872]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [esi+172]
	xor eax, DWORD PTR [edi+876]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [esi+176]
	xor eax, DWORD PTR [edi+880]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [esi+180]
	xor eax, DWORD PTR [edi+884]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [esi+184]
	xor eax, DWORD PTR [edi+888]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [esi+188]
	xor eax, DWORD PTR [edi+892]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [esi+192]
	xor eax, DWORD PTR [edi+896]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [esi+196]
	xor eax, DWORD PTR [edi+900]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [esi+200]
	xor eax, DWORD PTR [edi+904]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [esi+204]
	xor eax, DWORD PTR [edi+908]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [esi+208]
	xor eax, DWORD PTR [edi+912]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [esi+212]
	xor eax, DWORD PTR [edi+916]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [esi+216]
	xor eax, DWORD PTR [edi+920]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [esi+220]
	xor eax, DWORD PTR [edi+924]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [esi+224]
	xor eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [esi+228]
	xor eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [esi+232]
	xor eax, DWORD PTR [edi+936]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [esi+236]
	xor eax, DWORD PTR [edi+940]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [esi+240]
	xor eax, DWORD PTR [edi+944]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [esi+244]
	xor eax, DWORD PTR [edi+948]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [esi+248]
	xor eax, DWORD PTR [edi+952]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [esi+252]
	xor eax, DWORD PTR [edi+956]
	mov DWORD PTR [esi+252], eax
	add esi, 256
	sub ebp, 16
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 16
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 8
	jb 26f
28:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 8
	jae 28b
	jmp 27f
26:
27:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 4
	jb 29f
211:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 4
	jae 211b
	jmp 210f
29:
210:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 2
	jb 212f
214:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 2
	jae 214b
	jmp 213f
212:
213:
	mov eax, DWORD PTR [edi+1524]
	test eax, eax
	je 215f
217:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+1540]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1536]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+1532]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+1528]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+1528], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jne 217b
	jmp 216f
215:
216:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	movdqu XMMWORD PTR [esp+1436], xmm0
	movdqu XMMWORD PTR [esp+1452], xmm0
	movdqu XMMWORD PTR [esp+1468], xmm0
	movdqu XMMWORD PTR [esp+1484], xmm0
	movdqu XMMWORD PTR [esp+1500], xmm0
	movdqu XMMWORD PTR [esp+1516], xmm0
	movdqu XMMWORD PTR [esp+1532], xmm0
	movdqu XMMWORD PTR [esp+1548], xmm0
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	lea esp, [esp+1572]
	ret
	.p2align 6
