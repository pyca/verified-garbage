// The functions of `src/triple_des_ofb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_ofb_ssse3:
	lea esp, [esp-968]
	mov eax, DWORD PTR [esp+972]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+976]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+980]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+984]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+904], ebx
	mov DWORD PTR [eax+908], esi
	mov DWORD PTR [eax+912], edi
	mov DWORD PTR [eax+916], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+932], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_TRIPLE_DES_SSSE3}
	pop ecx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esp+4]
	mov edx, eax
	add edx, 248
	mov esi, edi
	add esi, 48
	mov ecx, 16
20:
	mov ebp, DWORD PTR [eax]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi], ebx
	mov ebp, DWORD PTR [eax]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+4], ebx
	mov ebp, DWORD PTR [edx]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [edx]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [edx]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [edx+4]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [edx+4]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+128], ebx
	mov ebp, DWORD PTR [edx]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [edx]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [edx]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [edx+4]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+132], ebx
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+256], ebx
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+260], ebx
	add eax, 8
	sub edx, 8
	add esi, 8
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+924], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+12], eax
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+12]
	bswap esi
	bswap ecx
	mov eax, esi
	shr eax, 4
	xor eax, ecx
	and eax, 252645135
	xor ecx, eax
	ror eax, 28
	xor esi, eax
	mov eax, esi
	shr eax, 16
	xor eax, ecx
	and eax, 65535
	xor ecx, eax
	ror eax, 16
	xor esi, eax
	mov eax, ecx
	shr eax, 2
	xor eax, esi
	and eax, 858993459
	xor esi, eax
	ror eax, 30
	xor ecx, eax
	mov eax, ecx
	shr eax, 8
	xor eax, esi
	and eax, 16711935
	xor esi, eax
	ror eax, 24
	xor ecx, eax
	mov eax, esi
	shr eax, 1
	xor eax, ecx
	and eax, 1431655765
	xor ecx, eax
	ror eax, 31
	xor esi, eax
	ror esi, 1
	ror ecx, 1
	movd xmm0, esi
	movdqu XMMWORD PTR [edi+32], xmm0
	movd xmm7, ecx
	mov ebp, edi
	add ebp, 48
	mov edx, 3
24:
	mov ecx, 8
25:
	movdqu XMMWORD PTR [edi+16], xmm7
	pshufd xmm0, xmm7, 0
	psrld xmm7, 2
	psrlq xmm0, 30
	punpckldq xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [ebx]
	pand xmm7, xmm6
	movq xmm6, QWORD PTR [ebp]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm7
	paddd xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm7
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm7
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm7
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [ebx+256]
	pshufb xmm1, xmm7
	pxor xmm1, xmm4
	paddd xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm7
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm7
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm7
	pxor xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm7
	pxor xmm4, xmm1
	paddd xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pshufb xmm1, xmm7
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm7
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm7
	pxor xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+288]
	pand xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pand xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pand xmm4, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm4
	pxor xmm1, xmm3
	pshufd xmm0, xmm1, 225
	pxor xmm0, xmm1
	movdqa xmm5, xmm0
	psrlq xmm5, 7
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pand xmm5, xmm6
	movdqa xmm2, xmm0
	psrlq xmm2, 15
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pand xmm2, xmm6
	pxor xmm5, xmm2
	movdqa xmm4, xmm0
	psrlq xmm4, 16
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pand xmm4, xmm6
	movdqa xmm3, xmm0
	psrlq xmm3, 23
	movdqu xmm6, XMMWORD PTR [ebx+400]
	pand xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm5, xmm4
	movdqa xmm1, xmm0
	psrlq xmm1, 27
	movdqu xmm6, XMMWORD PTR [ebx+416]
	pand xmm1, xmm6
	psrlq xmm0, 30
	movdqu xmm6, XMMWORD PTR [ebx+432]
	pand xmm0, xmm6
	pxor xmm1, xmm0
	movdqu xmm7, XMMWORD PTR [edi+32]
	pxor xmm7, xmm1
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [edi+32], xmm7
	pshufd xmm0, xmm7, 0
	psrld xmm7, 2
	psrlq xmm0, 30
	punpckldq xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [ebx]
	pand xmm7, xmm6
	movq xmm6, QWORD PTR [ebp+8]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm7
	paddd xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm7
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm7
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm7
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [ebx+256]
	pshufb xmm1, xmm7
	pxor xmm1, xmm4
	paddd xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm7
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm7
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm7
	pxor xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm7
	pxor xmm4, xmm1
	paddd xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pshufb xmm1, xmm7
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm7
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm7
	pxor xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+288]
	pand xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pand xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pand xmm4, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm4
	pxor xmm1, xmm3
	pshufd xmm0, xmm1, 225
	pxor xmm0, xmm1
	movdqa xmm5, xmm0
	psrlq xmm5, 7
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pand xmm5, xmm6
	movdqa xmm2, xmm0
	psrlq xmm2, 15
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pand xmm2, xmm6
	pxor xmm5, xmm2
	movdqa xmm4, xmm0
	psrlq xmm4, 16
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pand xmm4, xmm6
	movdqa xmm3, xmm0
	psrlq xmm3, 23
	movdqu xmm6, XMMWORD PTR [ebx+400]
	pand xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm5, xmm4
	movdqa xmm1, xmm0
	psrlq xmm1, 27
	movdqu xmm6, XMMWORD PTR [ebx+416]
	pand xmm1, xmm6
	psrlq xmm0, 30
	movdqu xmm6, XMMWORD PTR [ebx+432]
	pand xmm0, xmm6
	pxor xmm1, xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	pxor xmm7, xmm1
	pxor xmm7, xmm5
	add ebp, 16
	sub ecx, 1
	jne 25b
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+32], xmm7
	movdqa xmm7, xmm0
	sub edx, 1
	jne 24b
	movdqu XMMWORD PTR [edi+16], xmm7
	mov esi, DWORD PTR [edi+32]
	mov ecx, DWORD PTR [edi+16]
	ror esi, 31
	ror ecx, 31
	mov eax, esi
	shr eax, 1
	xor eax, ecx
	and eax, 1431655765
	xor ecx, eax
	ror eax, 31
	xor esi, eax
	mov eax, ecx
	shr eax, 8
	xor eax, esi
	and eax, 16711935
	xor esi, eax
	ror eax, 24
	xor ecx, eax
	mov eax, ecx
	shr eax, 2
	xor eax, esi
	and eax, 858993459
	xor esi, eax
	ror eax, 30
	xor ecx, eax
	mov eax, esi
	shr eax, 16
	xor eax, ecx
	and eax, 65535
	xor ecx, eax
	ror eax, 16
	xor esi, eax
	mov eax, esi
	shr eax, 4
	xor eax, ecx
	and eax, 252645135
	xor ecx, eax
	ror eax, 28
	xor esi, eax
	bswap esi
	bswap ecx
	mov DWORD PTR [edi+8], esi
	mov DWORD PTR [edi+12], ecx
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+904]
	mov esi, DWORD PTR [edi+908]
	mov ebp, DWORD PTR [edi+916]
	mov edi, DWORD PTR [edi+912]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	movdqu XMMWORD PTR [esp+440], xmm0
	movdqu XMMWORD PTR [esp+456], xmm0
	movdqu XMMWORD PTR [esp+472], xmm0
	movdqu XMMWORD PTR [esp+488], xmm0
	movdqu XMMWORD PTR [esp+504], xmm0
	movdqu XMMWORD PTR [esp+520], xmm0
	movdqu XMMWORD PTR [esp+536], xmm0
	movdqu XMMWORD PTR [esp+552], xmm0
	movdqu XMMWORD PTR [esp+568], xmm0
	movdqu XMMWORD PTR [esp+584], xmm0
	movdqu XMMWORD PTR [esp+600], xmm0
	movdqu XMMWORD PTR [esp+616], xmm0
	movdqu XMMWORD PTR [esp+632], xmm0
	movdqu XMMWORD PTR [esp+648], xmm0
	movdqu XMMWORD PTR [esp+664], xmm0
	movdqu XMMWORD PTR [esp+680], xmm0
	movdqu XMMWORD PTR [esp+696], xmm0
	movdqu XMMWORD PTR [esp+712], xmm0
	movdqu XMMWORD PTR [esp+728], xmm0
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	lea esp, [esp+968]
	lea esp, [esp-984]
	mov ecx, 0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	lea esp, [esp+984]
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

vg_triple_des_ofb:
	lea esp, [esp-968]
	mov eax, DWORD PTR [esp+972]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+976]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+980]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+984]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+904], ebx
	mov DWORD PTR [eax+908], esi
	mov DWORD PTR [eax+912], edi
	mov DWORD PTR [eax+916], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+932], eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [ecx+32]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [ecx+36]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [ecx+40]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [ecx+44]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [ecx+48]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [ecx+52]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [ecx+56]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [ecx+60]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [ecx+64]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [ecx+68]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [ecx+72]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [ecx+76]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [ecx+80]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [ecx+84]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [ecx+88]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [ecx+92]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [ecx+96]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [ecx+100]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [ecx+104]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [ecx+108]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [ecx+112]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [ecx+116]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [ecx+120]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [ecx+124]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [ecx+128]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [ecx+132]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [ecx+136]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [ecx+140]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [ecx+144]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [ecx+148]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [ecx+152]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [ecx+156]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [ecx+160]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [ecx+164]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [ecx+168]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [ecx+172]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [ecx+176]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [ecx+180]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [ecx+184]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [ecx+188]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [ecx+192]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [ecx+196]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [ecx+200]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [ecx+204]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [ecx+208]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [ecx+212]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [ecx+216]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [ecx+220]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [ecx+224]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [ecx+228]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [ecx+232]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [ecx+236]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [ecx+240]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [ecx+244]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [ecx+248]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [ecx+252]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [ecx+256]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [ecx+260]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [ecx+264]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [ecx+268]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [ecx+272]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [ecx+276]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [ecx+280]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [ecx+284]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [ecx+288]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [ecx+292]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [ecx+296]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [ecx+300]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [ecx+304]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [ecx+308]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [ecx+312]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [ecx+316]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [ecx+320]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [ecx+324]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [ecx+328]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [ecx+332]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [ecx+336]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ecx+340]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ecx+344]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ecx+348]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ecx+352]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ecx+356]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [ecx+360]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [ecx+364]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [ecx+368]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [ecx+372]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [ecx+376]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [ecx+380]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+924], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+516], eax
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, edi
	mov ecx, edi
	add ecx, 512
	mov edx, edi
	add edx, 520
	push eax
	push ecx
	push edx
	call {vg_triple_des_encrypt_block}
	pop eax
	pop eax
	pop eax
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+512]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+516]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 1
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+904]
	mov esi, DWORD PTR [edi+908]
	mov ebp, DWORD PTR [edi+916]
	mov edi, DWORD PTR [edi+912]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	movdqu XMMWORD PTR [esp+440], xmm0
	movdqu XMMWORD PTR [esp+456], xmm0
	movdqu XMMWORD PTR [esp+472], xmm0
	movdqu XMMWORD PTR [esp+488], xmm0
	movdqu XMMWORD PTR [esp+504], xmm0
	movdqu XMMWORD PTR [esp+520], xmm0
	movdqu XMMWORD PTR [esp+536], xmm0
	movdqu XMMWORD PTR [esp+552], xmm0
	movdqu XMMWORD PTR [esp+568], xmm0
	movdqu XMMWORD PTR [esp+584], xmm0
	movdqu XMMWORD PTR [esp+600], xmm0
	movdqu XMMWORD PTR [esp+616], xmm0
	movdqu XMMWORD PTR [esp+632], xmm0
	movdqu XMMWORD PTR [esp+648], xmm0
	movdqu XMMWORD PTR [esp+664], xmm0
	movdqu XMMWORD PTR [esp+680], xmm0
	movdqu XMMWORD PTR [esp+696], xmm0
	movdqu XMMWORD PTR [esp+712], xmm0
	movdqu XMMWORD PTR [esp+728], xmm0
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	lea esp, [esp+968]
	lea esp, [esp-984]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	lea esp, [esp+984]
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

vg_triple_des_ofb_final_ssse3:
	lea esp, [esp-968]
	mov eax, DWORD PTR [esp+972]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+976]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+980]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+984]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+904], ebx
	mov DWORD PTR [eax+908], esi
	mov DWORD PTR [eax+912], edi
	mov DWORD PTR [eax+916], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+932], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_TRIPLE_DES_SSSE3}
	pop ecx
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [esp+4]
	mov edx, eax
	add edx, 248
	mov esi, edi
	add esi, 48
	mov ecx, 16
20:
	mov ebp, DWORD PTR [eax]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi], ebx
	mov ebp, DWORD PTR [eax]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+4]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+4], ebx
	mov ebp, DWORD PTR [edx]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [edx]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [edx]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [edx+4]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [edx+4]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+128], ebx
	mov ebp, DWORD PTR [edx]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [edx]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [edx]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [edx+4]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+132], ebx
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 6
	and ebp, 63
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 10
	and ebp, 16128
	or ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 14
	and ebp, 196608
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 14
	and ebp, 3932160
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 18
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+256], ebx
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 4
	and ebp, 16128
	mov ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	and ebp, 63
	or ebx, ebp
	mov ebp, DWORD PTR [eax+256]
	shr ebp, 8
	and ebp, 4128768
	or ebx, ebp
	mov ebp, DWORD PTR [eax+260]
	ror ebp, 12
	and ebp, 1056964608
	or ebx, ebp
	or ebx, 1077952576
	mov DWORD PTR [esi+260], ebx
	add eax, 8
	sub edx, 8
	add esi, 8
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+924], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+12], eax
	mov ebx, DWORD PTR [edi]
	mov esi, DWORD PTR [edi+8]
	mov ecx, DWORD PTR [edi+12]
	bswap esi
	bswap ecx
	mov eax, esi
	shr eax, 4
	xor eax, ecx
	and eax, 252645135
	xor ecx, eax
	ror eax, 28
	xor esi, eax
	mov eax, esi
	shr eax, 16
	xor eax, ecx
	and eax, 65535
	xor ecx, eax
	ror eax, 16
	xor esi, eax
	mov eax, ecx
	shr eax, 2
	xor eax, esi
	and eax, 858993459
	xor esi, eax
	ror eax, 30
	xor ecx, eax
	mov eax, ecx
	shr eax, 8
	xor eax, esi
	and eax, 16711935
	xor esi, eax
	ror eax, 24
	xor ecx, eax
	mov eax, esi
	shr eax, 1
	xor eax, ecx
	and eax, 1431655765
	xor ecx, eax
	ror eax, 31
	xor esi, eax
	ror esi, 1
	ror ecx, 1
	movd xmm0, esi
	movdqu XMMWORD PTR [edi+32], xmm0
	movd xmm7, ecx
	mov ebp, edi
	add ebp, 48
	mov edx, 3
24:
	mov ecx, 8
25:
	movdqu XMMWORD PTR [edi+16], xmm7
	pshufd xmm0, xmm7, 0
	psrld xmm7, 2
	psrlq xmm0, 30
	punpckldq xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [ebx]
	pand xmm7, xmm6
	movq xmm6, QWORD PTR [ebp]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm7
	paddd xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm7
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm7
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm7
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [ebx+256]
	pshufb xmm1, xmm7
	pxor xmm1, xmm4
	paddd xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm7
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm7
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm7
	pxor xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm7
	pxor xmm4, xmm1
	paddd xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pshufb xmm1, xmm7
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm7
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm7
	pxor xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+288]
	pand xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pand xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pand xmm4, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm4
	pxor xmm1, xmm3
	pshufd xmm0, xmm1, 225
	pxor xmm0, xmm1
	movdqa xmm5, xmm0
	psrlq xmm5, 7
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pand xmm5, xmm6
	movdqa xmm2, xmm0
	psrlq xmm2, 15
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pand xmm2, xmm6
	pxor xmm5, xmm2
	movdqa xmm4, xmm0
	psrlq xmm4, 16
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pand xmm4, xmm6
	movdqa xmm3, xmm0
	psrlq xmm3, 23
	movdqu xmm6, XMMWORD PTR [ebx+400]
	pand xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm5, xmm4
	movdqa xmm1, xmm0
	psrlq xmm1, 27
	movdqu xmm6, XMMWORD PTR [ebx+416]
	pand xmm1, xmm6
	psrlq xmm0, 30
	movdqu xmm6, XMMWORD PTR [ebx+432]
	pand xmm0, xmm6
	pxor xmm1, xmm0
	movdqu xmm7, XMMWORD PTR [edi+32]
	pxor xmm7, xmm1
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [edi+32], xmm7
	pshufd xmm0, xmm7, 0
	psrld xmm7, 2
	psrlq xmm0, 30
	punpckldq xmm7, xmm0
	movdqu xmm6, XMMWORD PTR [ebx]
	pand xmm7, xmm6
	movq xmm6, QWORD PTR [ebp+8]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm7
	paddd xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm7
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm7
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm7
	pxor xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [ebx+256]
	pshufb xmm1, xmm7
	pxor xmm1, xmm4
	paddd xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm7
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm7
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm7
	pxor xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm7
	pxor xmm4, xmm1
	paddd xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pshufb xmm1, xmm7
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm7
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm7
	pxor xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+288]
	pand xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pand xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pand xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pand xmm4, xmm6
	pxor xmm1, xmm2
	pxor xmm3, xmm4
	pxor xmm1, xmm3
	pshufd xmm0, xmm1, 225
	pxor xmm0, xmm1
	movdqa xmm5, xmm0
	psrlq xmm5, 7
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pand xmm5, xmm6
	movdqa xmm2, xmm0
	psrlq xmm2, 15
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pand xmm2, xmm6
	pxor xmm5, xmm2
	movdqa xmm4, xmm0
	psrlq xmm4, 16
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pand xmm4, xmm6
	movdqa xmm3, xmm0
	psrlq xmm3, 23
	movdqu xmm6, XMMWORD PTR [ebx+400]
	pand xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm5, xmm4
	movdqa xmm1, xmm0
	psrlq xmm1, 27
	movdqu xmm6, XMMWORD PTR [ebx+416]
	pand xmm1, xmm6
	psrlq xmm0, 30
	movdqu xmm6, XMMWORD PTR [ebx+432]
	pand xmm0, xmm6
	pxor xmm1, xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	pxor xmm7, xmm1
	pxor xmm7, xmm5
	add ebp, 16
	sub ecx, 1
	jne 25b
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+32], xmm7
	movdqa xmm7, xmm0
	sub edx, 1
	jne 24b
	movdqu XMMWORD PTR [edi+16], xmm7
	mov esi, DWORD PTR [edi+32]
	mov ecx, DWORD PTR [edi+16]
	ror esi, 31
	ror ecx, 31
	mov eax, esi
	shr eax, 1
	xor eax, ecx
	and eax, 1431655765
	xor ecx, eax
	ror eax, 31
	xor esi, eax
	mov eax, ecx
	shr eax, 8
	xor eax, esi
	and eax, 16711935
	xor esi, eax
	ror eax, 24
	xor ecx, eax
	mov eax, ecx
	shr eax, 2
	xor eax, esi
	and eax, 858993459
	xor esi, eax
	ror eax, 30
	xor ecx, eax
	mov eax, esi
	shr eax, 16
	xor eax, ecx
	and eax, 65535
	xor ecx, eax
	ror eax, 16
	xor esi, eax
	mov eax, esi
	shr eax, 4
	xor eax, ecx
	and eax, 252645135
	xor ecx, eax
	ror eax, 28
	xor esi, eax
	bswap esi
	bswap ecx
	mov DWORD PTR [edi+8], esi
	mov DWORD PTR [edi+12], ecx
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	cmp ebp, 8
	jb 26f
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
	jmp 27f
26:
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+932], eax
	mov ebx, edi
	add ebx, 8
28:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 28b
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
27:
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+904]
	mov esi, DWORD PTR [edi+908]
	mov ebp, DWORD PTR [edi+916]
	mov edi, DWORD PTR [edi+912]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	movdqu XMMWORD PTR [esp+440], xmm0
	movdqu XMMWORD PTR [esp+456], xmm0
	movdqu XMMWORD PTR [esp+472], xmm0
	movdqu XMMWORD PTR [esp+488], xmm0
	movdqu XMMWORD PTR [esp+504], xmm0
	movdqu XMMWORD PTR [esp+520], xmm0
	movdqu XMMWORD PTR [esp+536], xmm0
	movdqu XMMWORD PTR [esp+552], xmm0
	movdqu XMMWORD PTR [esp+568], xmm0
	movdqu XMMWORD PTR [esp+584], xmm0
	movdqu XMMWORD PTR [esp+600], xmm0
	movdqu XMMWORD PTR [esp+616], xmm0
	movdqu XMMWORD PTR [esp+632], xmm0
	movdqu XMMWORD PTR [esp+648], xmm0
	movdqu XMMWORD PTR [esp+664], xmm0
	movdqu XMMWORD PTR [esp+680], xmm0
	movdqu XMMWORD PTR [esp+696], xmm0
	movdqu XMMWORD PTR [esp+712], xmm0
	movdqu XMMWORD PTR [esp+728], xmm0
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	lea esp, [esp+968]
	lea esp, [esp-984]
	mov ecx, 0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	lea esp, [esp+984]
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

vg_triple_des_ofb_final:
	lea esp, [esp-968]
	mov eax, DWORD PTR [esp+972]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+976]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+980]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+984]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+904], ebx
	mov DWORD PTR [eax+908], esi
	mov DWORD PTR [eax+912], edi
	mov DWORD PTR [eax+916], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+932], eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+524], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+544], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+548], eax
	mov eax, DWORD PTR [ecx+32]
	mov DWORD PTR [edi+552], eax
	mov eax, DWORD PTR [ecx+36]
	mov DWORD PTR [edi+556], eax
	mov eax, DWORD PTR [ecx+40]
	mov DWORD PTR [edi+560], eax
	mov eax, DWORD PTR [ecx+44]
	mov DWORD PTR [edi+564], eax
	mov eax, DWORD PTR [ecx+48]
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [ecx+52]
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [ecx+56]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [ecx+60]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [ecx+64]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [ecx+68]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [ecx+72]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [ecx+76]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [ecx+80]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [ecx+84]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [ecx+88]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [ecx+92]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [ecx+96]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [ecx+100]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [ecx+104]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [ecx+108]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [ecx+112]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [ecx+116]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [ecx+120]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [ecx+124]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [ecx+128]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [ecx+132]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [ecx+136]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [ecx+140]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [ecx+144]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [ecx+148]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [ecx+152]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [ecx+156]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [ecx+160]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [ecx+164]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [ecx+168]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [ecx+172]
	mov DWORD PTR [edi+692], eax
	mov eax, DWORD PTR [ecx+176]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [ecx+180]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [ecx+184]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [ecx+188]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [ecx+192]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [ecx+196]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [ecx+200]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [ecx+204]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [ecx+208]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [ecx+212]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [ecx+216]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [ecx+220]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [ecx+224]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [ecx+228]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [ecx+232]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [ecx+236]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [ecx+240]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [ecx+244]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [ecx+248]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [ecx+252]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [ecx+256]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [ecx+260]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [ecx+264]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [ecx+268]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [ecx+272]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [ecx+276]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [ecx+280]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [ecx+284]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [ecx+288]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [ecx+292]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [ecx+296]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [ecx+300]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [ecx+304]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [ecx+308]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [ecx+312]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [ecx+316]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [ecx+320]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [ecx+324]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [ecx+328]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [ecx+332]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [ecx+336]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ecx+340]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ecx+344]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ecx+348]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ecx+352]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ecx+356]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [ecx+360]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [ecx+364]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [ecx+368]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [ecx+372]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [ecx+376]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [ecx+380]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+924], eax
	test eax, eax
	je 20f
22:
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [edi+512], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [edi+516], eax
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	mov eax, edi
	mov ecx, edi
	add ecx, 512
	mov edx, edi
	add edx, 520
	push eax
	push ecx
	push edx
	call {vg_triple_des_encrypt_block}
	pop eax
	pop eax
	pop eax
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
	mov esi, DWORD PTR [edi+920]
	mov ebp, DWORD PTR [edi+924]
	cmp ebp, 8
	jb 23f
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+512]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+516]
	mov DWORD PTR [esi+4], eax
	add esi, 8
	sub ebp, 8
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
	jmp 24f
23:
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+932], eax
	mov ebx, edi
	add ebx, 512
25:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 25b
	mov DWORD PTR [edi+920], esi
	mov DWORD PTR [edi+924], ebp
24:
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+4], eax
	mov ebx, DWORD PTR [edi+904]
	mov esi, DWORD PTR [edi+908]
	mov ebp, DWORD PTR [edi+916]
	mov edi, DWORD PTR [edi+912]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	movdqu XMMWORD PTR [esp+440], xmm0
	movdqu XMMWORD PTR [esp+456], xmm0
	movdqu XMMWORD PTR [esp+472], xmm0
	movdqu XMMWORD PTR [esp+488], xmm0
	movdqu XMMWORD PTR [esp+504], xmm0
	movdqu XMMWORD PTR [esp+520], xmm0
	movdqu XMMWORD PTR [esp+536], xmm0
	movdqu XMMWORD PTR [esp+552], xmm0
	movdqu XMMWORD PTR [esp+568], xmm0
	movdqu XMMWORD PTR [esp+584], xmm0
	movdqu XMMWORD PTR [esp+600], xmm0
	movdqu XMMWORD PTR [esp+616], xmm0
	movdqu XMMWORD PTR [esp+632], xmm0
	movdqu XMMWORD PTR [esp+648], xmm0
	movdqu XMMWORD PTR [esp+664], xmm0
	movdqu XMMWORD PTR [esp+680], xmm0
	movdqu XMMWORD PTR [esp+696], xmm0
	movdqu XMMWORD PTR [esp+712], xmm0
	movdqu XMMWORD PTR [esp+728], xmm0
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	lea esp, [esp+968]
	lea esp, [esp-984]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	lea esp, [esp+984]
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
