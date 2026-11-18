// The functions of `src/internal/vg_ecdsa_p192_sign_k.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_sign_k:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_P192_COMB}
	pop ecx
	mov edx, DWORD PTR [esp+20]
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+16]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+828], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+876], eax
	mov eax, -1
	mov DWORD PTR [edi+64], eax
	mov eax, -1
	mov DWORD PTR [edi+68], eax
	mov eax, -2
	mov DWORD PTR [edi+72], eax
	mov eax, -1
	mov DWORD PTR [edi+76], eax
	mov eax, -1
	mov DWORD PTR [edi+80], eax
	mov eax, -1
	mov DWORD PTR [edi+84], eax
	mov eax, -1261295567
	mov DWORD PTR [edi+88], eax
	mov eax, 342608305
	mov DWORD PTR [edi+92], eax
	mov eax, -1713440714
	mov DWORD PTR [edi+96], eax
	mov eax, -1
	mov DWORD PTR [edi+100], eax
	mov eax, -1
	mov DWORD PTR [edi+104], eax
	mov eax, -1
	mov DWORD PTR [edi+108], eax
	mov eax, 0
	mov DWORD PTR [edi+136], eax
	mov eax, 0
	mov DWORD PTR [edi+140], eax
	mov eax, 0
	mov DWORD PTR [edi+144], eax
	mov eax, 0
	mov DWORD PTR [edi+148], eax
	mov eax, 0
	mov DWORD PTR [edi+152], eax
	mov eax, 0
	mov DWORD PTR [edi+156], eax
	mov eax, 1
	mov DWORD PTR [edi+160], eax
	mov eax, 0
	mov DWORD PTR [edi+164], eax
	mov eax, 0
	mov DWORD PTR [edi+168], eax
	mov eax, 0
	mov DWORD PTR [edi+172], eax
	mov eax, 0
	mov DWORD PTR [edi+176], eax
	mov eax, 0
	mov DWORD PTR [edi+180], eax
	mov eax, 1
	mov DWORD PTR [edi+184], eax
	mov eax, 0
	mov DWORD PTR [edi+188], eax
	mov eax, 1
	mov DWORD PTR [edi+192], eax
	mov eax, 0
	mov DWORD PTR [edi+196], eax
	mov eax, 0
	mov DWORD PTR [edi+200], eax
	mov eax, 0
	mov DWORD PTR [edi+204], eax
	mov eax, -4
	mov DWORD PTR [edi+208], eax
	mov eax, -1
	mov DWORD PTR [edi+212], eax
	mov eax, -5
	mov DWORD PTR [edi+216], eax
	mov eax, -1
	mov DWORD PTR [edi+220], eax
	mov eax, -1
	mov DWORD PTR [edi+224], eax
	mov eax, -1
	mov DWORD PTR [edi+228], eax
	mov eax, -190206007
	mov DWORD PTR [edi+232], eax
	mov eax, 680373267
	mov DWORD PTR [edi+236], eax
	mov eax, 1259749544
	mov DWORD PTR [edi+240], eax
	mov eax, 1468360982
	mov DWORD PTR [edi+244], eax
	mov eax, 121770900
	mov DWORD PTR [edi+248], eax
	mov eax, 1532677200
	mov DWORD PTR [edi+252], eax
	mov eax, 858759432
	mov DWORD PTR [edi+256], eax
	mov eax, 227324684
	mov DWORD PTR [edi+260], eax
	mov eax, 1993419017
	mov DWORD PTR [edi+264], eax
	mov eax, -1974742025
	mov DWORD PTR [edi+268], eax
	mov eax, -204334857
	mov DWORD PTR [edi+272], eax
	mov eax, -1790129927
	mov DWORD PTR [edi+276], eax
	mov eax, 507650697
	mov DWORD PTR [edi+280], eax
	mov eax, 2064818999
	mov DWORD PTR [edi+284], eax
	mov eax, -1989742498
	mov DWORD PTR [edi+288], eax
	mov eax, -568150748
	mov DWORD PTR [edi+292], eax
	mov eax, 1793960013
	mov DWORD PTR [edi+296], eax
	mov eax, 1781087619
	mov DWORD PTR [edi+300], eax
	mov eax, -558671519
	mov DWORD PTR [edi+304], eax
	mov eax, -832128308
	mov DWORD PTR [edi+308], eax
	mov eax, -1153799186
	mov DWORD PTR [edi+312], eax
	mov eax, 1184295515
	mov DWORD PTR [edi+316], eax
	mov eax, -368737886
	mov DWORD PTR [edi+320], eax
	mov eax, 683562615
	mov DWORD PTR [edi+324], eax
	mov eax, 1261295567
	mov DWORD PTR [edi+328], eax
	mov eax, -342608306
	mov DWORD PTR [edi+332], eax
	mov eax, 1713440713
	mov DWORD PTR [edi+336], eax
	mov eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, -3
	mov DWORD PTR [edi+352], eax
	mov eax, -1
	mov DWORD PTR [edi+356], eax
	mov eax, -2
	mov DWORD PTR [edi+360], eax
	mov eax, -1
	mov DWORD PTR [edi+364], eax
	mov eax, -1
	mov DWORD PTR [edi+368], eax
	mov eax, -1
	mov DWORD PTR [edi+372], eax
	mov eax, -1261295569
	mov DWORD PTR [edi+376], eax
	mov eax, 342608305
	mov DWORD PTR [edi+380], eax
	mov eax, -1713440714
	mov DWORD PTR [edi+384], eax
	mov eax, -1
	mov DWORD PTR [edi+388], eax
	mov eax, -1
	mov DWORD PTR [edi+392], eax
	mov eax, -1
	mov DWORD PTR [edi+396], eax
	mov eax, 0
	mov DWORD PTR [edi+400], eax
	mov eax, 0
	mov DWORD PTR [edi+404], eax
	mov eax, 0
	mov DWORD PTR [edi+408], eax
	mov eax, 0
	mov DWORD PTR [edi+412], eax
	mov eax, 0
	mov DWORD PTR [edi+416], eax
	mov eax, 0
	mov DWORD PTR [edi+420], eax
	mov eax, 1
	mov DWORD PTR [edi+424], eax
	mov eax, 0
	mov DWORD PTR [edi+428], eax
	mov eax, 1
	mov DWORD PTR [edi+432], eax
	mov eax, 0
	mov DWORD PTR [edi+436], eax
	mov eax, 0
	mov DWORD PTR [edi+440], eax
	mov eax, 0
	mov DWORD PTR [edi+444], eax
	mov eax, 0
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 0
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov eax, -1
	mov DWORD PTR [edi+1120], eax
	mov esi, 24
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+808]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 20b
	mov esi, 24
21:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+352]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4292], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4293], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4294], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4295], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4296], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4297], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4298], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4299], dl
	test esi, esi
	jne 21b
	mov esi, 24
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+376]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4488], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4489], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4490], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4491], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4492], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4493], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4494], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4495], dl
	test esi, esi
	jne 22b
	mov eax, -190206007
	mov DWORD PTR [edi+1024], eax
	mov eax, 680373267
	mov DWORD PTR [edi+1028], eax
	mov eax, 1259749544
	mov DWORD PTR [edi+1032], eax
	mov eax, 1468360982
	mov DWORD PTR [edi+1036], eax
	mov eax, 121770900
	mov DWORD PTR [edi+1040], eax
	mov eax, 1532677200
	mov DWORD PTR [edi+1044], eax
	mov eax, 1951718549
	mov DWORD PTR [edi+400], eax
	mov eax, 2102261838
	mov DWORD PTR [edi+404], eax
	mov eax, 807037984
	mov DWORD PTR [edi+408], eax
	mov eax, 1060518963
	mov DWORD PTR [edi+412], eax
	mov eax, 602485952
	mov DWORD PTR [edi+416], eax
	mov eax, -408645293
	mov DWORD PTR [edi+420], eax
	mov eax, -1486989203
	mov DWORD PTR [edi+424], eax
	mov eax, 143323488
	mov DWORD PTR [edi+428], eax
	mov eax, -123283423
	mov DWORD PTR [edi+432], eax
	mov eax, 423143982
	mov DWORD PTR [edi+436], eax
	mov eax, -480835023
	mov DWORD PTR [edi+440], eax
	mov eax, 758643330
	mov DWORD PTR [edi+444], eax
	mov eax, 1
	mov DWORD PTR [edi+448], eax
	mov eax, 0
	mov DWORD PTR [edi+452], eax
	mov eax, 1
	mov DWORD PTR [edi+456], eax
	mov eax, 0
	mov DWORD PTR [edi+460], eax
	mov eax, 0
	mov DWORD PTR [edi+464], eax
	mov eax, 0
	mov DWORD PTR [edi+468], eax
	mov esi, 28
23:
	sub esi, 1
	cmp esi, 27
	je 24f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4102]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4101]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4100]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4099]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
	jmp 25f
24:
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	mov eax, 0
	add eax, eax
	movzx edx, BYTE PTR [ecx+4098]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4097]
	add eax, edx
	add eax, eax
	movzx edx, BYTE PTR [ecx+4096]
	add eax, edx
	sub eax, 64
	mov edx, eax
	shr edx, 31
	mov ebx, 0
	sub ebx, edx
	xor eax, ebx
	sub eax, ebx
	mov ebx, eax
25:
	mov eax, esi
	mov ecx, 3072
	mul ecx
	mov edx, DWORD PTR [edi+60]
	add edx, eax
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	mov ecx, 1
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+16]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+32]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 2
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+48]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+64]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+80]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 3
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+96]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+112]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+128]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 4
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+144]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+160]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+176]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 5
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+192]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+208]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+224]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 6
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+240]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+256]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+272]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 7
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+288]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+304]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+320]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 8
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+336]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+352]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+368]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 9
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+384]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+400]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+416]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 10
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+432]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+448]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+464]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 11
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+480]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+496]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+512]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 12
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+528]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+544]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+560]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 13
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+576]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+592]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+608]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 14
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+624]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+640]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+656]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 15
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+672]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+688]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+704]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 16
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+720]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+736]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+752]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 17
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+768]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+784]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+800]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 18
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+816]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+832]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+848]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 19
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+864]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+880]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+896]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 20
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+912]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+928]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+944]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 21
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+960]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+976]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+992]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 22
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1008]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1024]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1040]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 23
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1056]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1072]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1088]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 24
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1104]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1120]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1136]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 25
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1152]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1168]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1184]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 26
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1200]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1216]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1232]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 27
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1248]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1264]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1280]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 28
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1296]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1312]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1328]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 29
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1344]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1360]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1376]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 30
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1392]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1408]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1424]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 31
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1440]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1456]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1472]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 32
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1488]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1504]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1520]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 33
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1536]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1552]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1568]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 34
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1584]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1600]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1616]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 35
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1632]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1648]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1664]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 36
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1680]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1696]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1712]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 37
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1728]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1744]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1760]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 38
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1776]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1792]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1808]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 39
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1824]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1840]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1856]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 40
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1872]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1888]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1904]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 41
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1920]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1936]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1952]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 42
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+1968]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+1984]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2000]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 43
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2016]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2032]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2048]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 44
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2064]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2080]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2096]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 45
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2112]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2128]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2144]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 46
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2160]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2176]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2192]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 47
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2208]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2224]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2240]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 48
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2256]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2272]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2288]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 49
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2304]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2320]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2336]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 50
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2352]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2368]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2384]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 51
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2400]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2416]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2432]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 52
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2448]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2464]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2480]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 53
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2496]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2512]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2528]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 54
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2544]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2560]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2576]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 55
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2592]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2608]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2624]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 56
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2640]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2656]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2672]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 57
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2688]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2704]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2720]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 58
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2736]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2752]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2768]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 59
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2784]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2800]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2816]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 60
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2832]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2848]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2864]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 61
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2880]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2896]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2912]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 62
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2928]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2944]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2960]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 63
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+2976]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+2992]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3008]
	pand xmm6, xmm7
	por xmm2, xmm6
	mov ecx, 64
	xor ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm6, XMMWORD PTR [edx+3024]
	pand xmm6, xmm7
	por xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3040]
	pand xmm6, xmm7
	por xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edx+3056]
	pand xmm6, xmm7
	por xmm2, xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu XMMWORD PTR [edi+576], xmm2
	mov eax, 1
	mov DWORD PTR [edi+592], eax
	mov eax, 0
	mov DWORD PTR [edi+596], eax
	mov eax, 1
	mov DWORD PTR [edi+600], eax
	mov eax, 0
	mov DWORD PTR [edi+604], eax
	mov eax, 0
	mov DWORD PTR [edi+608], eax
	mov eax, 0
	mov DWORD PTR [edi+612], eax
	mov ecx, ebx
	cmp ecx, 1
	sbb ecx, ecx
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+592]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+596]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+600]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+604]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+608]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+612]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+136]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+140]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+144]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+148]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+608]
	mov edx, DWORD PTR [edi+152]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+612]
	mov edx, DWORD PTR [edi+156]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+612], eax
	mov eax, 568
	mov ecx, 136
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	cmp esi, 27
	je 26f
	mov eax, esi
	mov ecx, 7
	mul ecx
	mov ecx, eax
	add ecx, edi
	movzx eax, BYTE PTR [ecx+4102]
	sub eax, 1
	mov ecx, eax
	jmp 27f
26:
	mov ecx, -1
27:
	mov eax, DWORD PTR [edi+568]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+568], eax
	mov eax, DWORD PTR [edi+572]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+572], eax
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+800]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+804]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+588], eax
	mov eax, 544
	mov ecx, 400
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 424
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 448
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 424
	mov ecx, 400
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 568
	mov ecx, 544
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 616
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 688
	mov edx, 688
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 400
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 544
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 736
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 424
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 592
	mov ecx, 568
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 736
	mov edx, 736
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 208
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 1024
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 640
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 640
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 472
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 616
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 1024
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 640
	mov edx, 640
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 616
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 208
	mov edx, 664
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 664
	mov ecx, 712
	mov edx, 712
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 640
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 496
	mov edx, 496
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 712
	mov ecx, 736
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 472
	mov ecx, 688
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 472
	mov edx, 472
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 688
	mov edx, 616
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 520
	mov ecx, 736
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 616
	mov ecx, 520
	mov edx, 520
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+472]
	mov DWORD PTR [edi+400], eax
	mov eax, DWORD PTR [edi+476]
	mov DWORD PTR [edi+404], eax
	mov eax, DWORD PTR [edi+480]
	mov DWORD PTR [edi+408], eax
	mov eax, DWORD PTR [edi+484]
	mov DWORD PTR [edi+412], eax
	mov eax, DWORD PTR [edi+488]
	mov DWORD PTR [edi+416], eax
	mov eax, DWORD PTR [edi+492]
	mov DWORD PTR [edi+420], eax
	mov eax, DWORD PTR [edi+496]
	mov DWORD PTR [edi+424], eax
	mov eax, DWORD PTR [edi+500]
	mov DWORD PTR [edi+428], eax
	mov eax, DWORD PTR [edi+504]
	mov DWORD PTR [edi+432], eax
	mov eax, DWORD PTR [edi+508]
	mov DWORD PTR [edi+436], eax
	mov eax, DWORD PTR [edi+512]
	mov DWORD PTR [edi+440], eax
	mov eax, DWORD PTR [edi+516]
	mov DWORD PTR [edi+444], eax
	mov eax, DWORD PTR [edi+520]
	mov DWORD PTR [edi+448], eax
	mov eax, DWORD PTR [edi+524]
	mov DWORD PTR [edi+452], eax
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+456], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+460], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+464], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+468], eax
	test esi, esi
	jne 23b
	mov eax, DWORD PTR [edi+184]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+188]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+192]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+196]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+200]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+204]
	mov DWORD PTR [edi+780], eax
	mov esi, 192
28:
	sub esi, 1
	mov eax, 760
	mov ecx, 760
	mov edx, 760
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 448
	mov ecx, 760
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4292]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+768]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+772]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+776]
	mov edx, DWORD PTR [edi+800]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+780]
	mov edx, DWORD PTR [edi+804]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	test esi, esi
	jne 28b
	mov eax, 760
	mov ecx, 400
	mov edx, 880
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 880
	mov edx, 904
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 136
	mov ecx, 904
	mov edx, 928
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 808
	mov edx, 952
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+832]
	sub edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+836]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+840]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+844]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+848]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+852]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+832]
	or edx, DWORD PTR [edi+836]
	or edx, DWORD PTR [edi+840]
	or edx, DWORD PTR [edi+844]
	or edx, DWORD PTR [edi+848]
	or edx, DWORD PTR [edi+852]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+808]
	sub edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+812]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+816]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+820]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+824]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+828]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+808]
	or edx, DWORD PTR [edi+812]
	or edx, DWORD PTR [edi+816]
	or edx, DWORD PTR [edi+820]
	or edx, DWORD PTR [edi+824]
	or edx, DWORD PTR [edi+828]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov edx, DWORD PTR [edi+928]
	or edx, DWORD PTR [edi+932]
	or edx, DWORD PTR [edi+936]
	or edx, DWORD PTR [edi+940]
	or edx, DWORD PTR [edi+944]
	or edx, DWORD PTR [edi+948]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+780], eax
	mov esi, 192
29:
	sub esi, 1
	mov eax, 760
	mov ecx, 760
	mov edx, 760
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 952
	mov ecx, 760
	mov edx, 784
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4488]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+760]
	mov edx, DWORD PTR [edi+784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+764]
	mov edx, DWORD PTR [edi+788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [edi+768]
	mov edx, DWORD PTR [edi+792]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+772]
	mov edx, DWORD PTR [edi+796]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+776]
	mov edx, DWORD PTR [edi+800]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+780]
	mov edx, DWORD PTR [edi+804]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+780], eax
	test esi, esi
	jne 29b
	mov eax, 304
	mov ecx, 928
	mov edx, 976
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 832
	mov edx, 1000
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 304
	mov ecx, 856
	mov edx, 1024
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1000
	mov ecx, 976
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1048
	mov edx, 1048
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_add_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1048
	mov ecx, 760
	mov edx, 1072
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 160
	mov ecx, 1072
	mov edx, 1096
	push eax
	push ecx
	push edx
	push edi
	call {vg_p192_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1096]
	or edx, DWORD PTR [edi+1100]
	or edx, DWORD PTR [edi+1104]
	or edx, DWORD PTR [edi+1108]
	or edx, DWORD PTR [edi+1112]
	or edx, DWORD PTR [edi+1116]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+1120]
	and eax, edx
	mov DWORD PTR [edi+1120], eax
	mov ecx, DWORD PTR [edi+1120]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+928]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+20], eax
	mov eax, DWORD PTR [edi+932]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+16], eax
	mov eax, DWORD PTR [edi+936]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [edi+940]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [edi+944]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [edi+948]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [edi+1096]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+44], eax
	mov eax, DWORD PTR [edi+1100]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+40], eax
	mov eax, DWORD PTR [edi+1104]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+36], eax
	mov eax, DWORD PTR [edi+1108]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+32], eax
	mov eax, DWORD PTR [edi+1112]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+28], eax
	mov eax, DWORD PTR [edi+1116]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+24], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
