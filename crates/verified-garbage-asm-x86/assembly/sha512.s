// The functions of `src/sha512.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -1056596264
	mov DWORD PTR [eax], ecx
	mov ecx, -876896931
	mov DWORD PTR [eax+4], ecx
	mov ecx, 914150663
	mov DWORD PTR [eax+8], ecx
	mov ecx, 1654270250
	mov DWORD PTR [eax+12], ecx
	mov ecx, 812702999
	mov DWORD PTR [eax+16], ecx
	mov ecx, -1856437926
	mov DWORD PTR [eax+20], ecx
	mov ecx, -150054599
	mov DWORD PTR [eax+24], ecx
	mov ecx, 355462360
	mov DWORD PTR [eax+28], ecx
	mov ecx, -4191439
	mov DWORD PTR [eax+32], ecx
	mov ecx, 1731405415
	mov DWORD PTR [eax+36], ecx
	mov ecx, 1750603025
	mov DWORD PTR [eax+40], ecx
	mov ecx, -1900787065
	mov DWORD PTR [eax+44], ecx
	mov ecx, 1694076839
	mov DWORD PTR [eax+48], ecx
	mov ecx, -619958771
	mov DWORD PTR [eax+52], ecx
	mov ecx, -1090891868
	mov DWORD PTR [eax+56], ecx
	mov ecx, 1203062813
	mov DWORD PTR [eax+60], ecx
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

vg_sha512_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -205731576
	mov DWORD PTR [eax], ecx
	mov ecx, 1779033703
	mov DWORD PTR [eax+4], ecx
	mov ecx, -2067093701
	mov DWORD PTR [eax+8], ecx
	mov ecx, -1150833019
	mov DWORD PTR [eax+12], ecx
	mov ecx, -23791573
	mov DWORD PTR [eax+16], ecx
	mov ecx, 1013904242
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1595750129
	mov DWORD PTR [eax+24], ecx
	mov ecx, -1521486534
	mov DWORD PTR [eax+28], ecx
	mov ecx, -1377402159
	mov DWORD PTR [eax+32], ecx
	mov ecx, 1359893119
	mov DWORD PTR [eax+36], ecx
	mov ecx, 725511199
	mov DWORD PTR [eax+40], ecx
	mov ecx, -1694144372
	mov DWORD PTR [eax+44], ecx
	mov ecx, -79577749
	mov DWORD PTR [eax+48], ecx
	mov ecx, 528734635
	mov DWORD PTR [eax+52], ecx
	mov ecx, 327033209
	mov DWORD PTR [eax+56], ecx
	mov ecx, 1541459225
	mov DWORD PTR [eax+60], ecx
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

vg_sha512_224_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, 424955298
	mov DWORD PTR [eax], ecx
	mov ecx, -1942145080
	mov DWORD PTR [eax+4], ecx
	mov ecx, -1982016298
	mov DWORD PTR [eax+8], ecx
	mov ecx, 1944164710
	mov DWORD PTR [eax+12], ecx
	mov ecx, 855612546
	mov DWORD PTR [eax+16], ecx
	mov ecx, 502970286
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1479516111
	mov DWORD PTR [eax+24], ecx
	mov ecx, 1738396948
	mov DWORD PTR [eax+28], ecx
	mov ecx, 2077511080
	mov DWORD PTR [eax+32], ecx
	mov ecx, 258812777
	mov DWORD PTR [eax+36], ecx
	mov ecx, 79989058
	mov DWORD PTR [eax+40], ecx
	mov ecx, 2011393907
	mov DWORD PTR [eax+44], ecx
	mov ecx, 1780299464
	mov DWORD PTR [eax+48], ecx
	mov ecx, 1067287976
	mov DWORD PTR [eax+52], ecx
	mov ecx, -1848208735
	mov DWORD PTR [eax+56], ecx
	mov ecx, 286451373
	mov DWORD PTR [eax+60], ecx
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

vg_sha512_256_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, -64227540
	mov DWORD PTR [eax], ecx
	mov ecx, 573645204
	mov DWORD PTR [eax+4], ecx
	mov ecx, -934517566
	mov DWORD PTR [eax+8], ecx
	mov ecx, -1621794909
	mov DWORD PTR [eax+12], ecx
	mov ecx, 1867755857
	mov DWORD PTR [eax+16], ecx
	mov ecx, 596883563
	mov DWORD PTR [eax+20], ecx
	mov ecx, 1497426621
	mov DWORD PTR [eax+24], ecx
	mov ecx, -1774684391
	mov DWORD PTR [eax+28], ecx
	mov ecx, -1467023389
	mov DWORD PTR [eax+32], ecx
	mov ecx, -1775747358
	mov DWORD PTR [eax+36], ecx
	mov ecx, 1401305490
	mov DWORD PTR [eax+40], ecx
	mov ecx, -1101128155
	mov DWORD PTR [eax+44], ecx
	mov ecx, 746961066
	mov DWORD PTR [eax+48], ecx
	mov ecx, 721525244
	mov DWORD PTR [eax+52], ecx
	mov ecx, -2117784414
	mov DWORD PTR [eax+56], ecx
	mov ecx, 246885852
	mov DWORD PTR [eax+60], ecx
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

vg_sha512_update:
	lea esp, [esp-1404]
	mov eax, DWORD PTR [esp+1408]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1412]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1416]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1420]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1424]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+224], ebx
	mov DWORD PTR [eax+228], esi
	mov DWORD PTR [eax+232], edi
	mov DWORD PTR [eax+236], ebp
	mov ebx, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+8]
	and edi, 127
20:
	test edi, edi
	je 21f
	mov eax, 128
	sub eax, edi
	cmp esi, eax
	jb 23f
	jmp 24f
23:
	mov eax, esi
24:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 25f
27:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+64], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 128
	je 28f
	jmp 29f
28:
	mov eax, ebx
	add eax, 64
	mov edi, 0
	mov ecx, 1
29:
	jmp 22f
21:
	cmp esi, 128
	jae 210f
	mov eax, 128
	sub eax, edi
	cmp esi, eax
	jb 212f
	jmp 213f
212:
	mov eax, esi
213:
	sub esi, eax
	add edi, ebx
	test eax, eax
	je 214f
216:
	movzx ecx, BYTE PTR [ebp]
	mov BYTE PTR [edi+64], cl
	add ebp, 1
	add edi, 1
	sub eax, 1
	jne 216b
	jmp 215f
214:
215:
	sub edi, ebx
	mov ecx, 0
	cmp edi, 128
	je 217f
	jmp 218f
217:
	mov eax, ebx
	add eax, 64
	mov edi, 0
	mov ecx, 1
218:
	jmp 211f
210:
	mov eax, ebp
	mov ecx, esi
	and ecx, 127
	mov edx, esi
	sub edx, ecx
	add ebp, edx
	mov esi, ecx
	mov ecx, edx
	shr ecx, 7
211:
22:
	test ecx, ecx
	jne 219f
	jmp 220f
219:
	mov edx, DWORD PTR [esp+24]
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, 1
	test ecx, ecx
220:
	jne 20b
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+224]
	mov esi, DWORD PTR [eax+228]
	mov edi, DWORD PTR [eax+232]
	mov ebp, DWORD PTR [eax+236]
	lea esp, [esp+1404]
	pxor xmm0, xmm0
	lea esp, [esp-1424]
	movdqu XMMWORD PTR [esp], xmm0
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
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	movdqu XMMWORD PTR [esp+1408], xmm0
	lea esp, [esp+1424]
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

vg_sha512_finalize:
	lea esp, [esp-1400]
	mov eax, DWORD PTR [esp+1404]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1408]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1412]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1416]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+224], ebx
	mov DWORD PTR [eax+228], esi
	mov DWORD PTR [eax+232], edi
	mov DWORD PTR [eax+236], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+240], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+244], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+248], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 127
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+64], cl
	add edi, 1
	mov esi, 0
	cmp edi, 113
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 128
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 112
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+64], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, 0
	mov DWORD PTR [ebx+176], edx
	mov edx, ecx
	shr edx, 29
	bswap edx
	mov DWORD PTR [ebx+180], edx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+184], ecx
	bswap eax
	mov DWORD PTR [ebx+188], eax
29:
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+52]
	bswap ecx
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+48]
	bswap ecx
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+60]
	bswap ecx
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+56]
	bswap ecx
	mov DWORD PTR [eax+60], ecx
	mov ebx, DWORD PTR [ebp+224]
	mov esi, DWORD PTR [ebp+228]
	mov edi, DWORD PTR [ebp+232]
	mov ebp, DWORD PTR [ebp+236]
	lea esp, [esp+1400]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1420]
	movdqu XMMWORD PTR [esp], xmm0
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
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	lea esp, [esp+1420]
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

vg_sha384_finalize:
	lea esp, [esp-1400]
	mov eax, DWORD PTR [esp+1404]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1408]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1412]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1416]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+224], ebx
	mov DWORD PTR [eax+228], esi
	mov DWORD PTR [eax+232], edi
	mov DWORD PTR [eax+236], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+240], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+244], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+248], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 127
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+64], cl
	add edi, 1
	mov esi, 0
	cmp edi, 113
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 128
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 112
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+64], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, 0
	mov DWORD PTR [ebx+176], edx
	mov edx, ecx
	shr edx, 29
	bswap edx
	mov DWORD PTR [ebx+180], edx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+184], ecx
	bswap eax
	mov DWORD PTR [ebx+188], eax
29:
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+36]
	bswap ecx
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+32]
	bswap ecx
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+44]
	bswap ecx
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+40]
	bswap ecx
	mov DWORD PTR [eax+44], ecx
	mov ebx, DWORD PTR [ebp+224]
	mov esi, DWORD PTR [ebp+228]
	mov edi, DWORD PTR [ebp+232]
	mov ebp, DWORD PTR [ebp+236]
	lea esp, [esp+1400]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1420]
	movdqu XMMWORD PTR [esp], xmm0
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
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	lea esp, [esp+1420]
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

vg_sha512_256_finalize:
	lea esp, [esp-1400]
	mov eax, DWORD PTR [esp+1404]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1408]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1412]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1416]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+224], ebx
	mov DWORD PTR [eax+228], esi
	mov DWORD PTR [eax+232], edi
	mov DWORD PTR [eax+236], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+240], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+244], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+248], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 127
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+64], cl
	add edi, 1
	mov esi, 0
	cmp edi, 113
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 128
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 112
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+64], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, 0
	mov DWORD PTR [ebx+176], edx
	mov edx, ecx
	shr edx, 29
	bswap edx
	mov DWORD PTR [ebx+180], edx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+184], ecx
	bswap eax
	mov DWORD PTR [ebx+188], eax
29:
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+24]
	bswap ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, DWORD PTR [ebp+224]
	mov esi, DWORD PTR [ebp+228]
	mov edi, DWORD PTR [ebp+232]
	mov ebp, DWORD PTR [ebp+236]
	lea esp, [esp+1400]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1420]
	movdqu XMMWORD PTR [esp], xmm0
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
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	lea esp, [esp+1420]
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

vg_sha512_224_finalize:
	lea esp, [esp-1400]
	mov eax, DWORD PTR [esp+1404]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1408]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1412]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1416]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+224], ebx
	mov DWORD PTR [eax+228], esi
	mov DWORD PTR [eax+232], edi
	mov DWORD PTR [eax+236], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+240], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+244], ecx
	mov ecx, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+248], ecx
	mov edi, DWORD PTR [esp+8]
	and edi, 127
	mov edx, ebx
	add edx, edi
	mov ecx, 128
	mov BYTE PTR [edx+64], cl
	add edi, 1
	mov esi, 0
	cmp edi, 113
	jae 20f
	jmp 21f
20:
	mov esi, 1
21:
22:
	mov eax, 128
	test esi, esi
	je 23f
	jmp 24f
23:
	mov eax, 112
24:
	mov ecx, 0
	sub eax, edi
	je 25f
27:
	mov edx, ebx
	add edx, edi
	mov BYTE PTR [edx+64], cl
	add edi, 1
	sub eax, 1
	jne 27b
	jmp 26f
25:
26:
	test esi, esi
	je 28f
	jmp 29f
28:
	mov eax, DWORD PTR [ebp+240]
	mov ecx, DWORD PTR [ebp+244]
	mov edx, 0
	mov DWORD PTR [ebx+176], edx
	mov edx, ecx
	shr edx, 29
	bswap edx
	mov DWORD PTR [ebx+180], edx
	add ecx, ecx
	add ecx, ecx
	add ecx, ecx
	mov edx, eax
	shr edx, 29
	or ecx, edx
	add eax, eax
	add eax, eax
	add eax, eax
	bswap ecx
	mov DWORD PTR [ebx+184], ecx
	bswap eax
	mov DWORD PTR [ebx+188], eax
29:
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, 0
	sub esi, 1
	je 22b
	mov eax, DWORD PTR [ebp+248]
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+20]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+28]
	bswap ecx
	mov DWORD PTR [eax+24], ecx
	mov ebx, DWORD PTR [ebp+224]
	mov esi, DWORD PTR [ebp+228]
	mov edi, DWORD PTR [ebp+232]
	mov ebp, DWORD PTR [ebp+236]
	lea esp, [esp+1400]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1420]
	movdqu XMMWORD PTR [esp], xmm0
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
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	movdqu XMMWORD PTR [esp+1152], xmm0
	movdqu XMMWORD PTR [esp+1168], xmm0
	movdqu XMMWORD PTR [esp+1184], xmm0
	movdqu XMMWORD PTR [esp+1200], xmm0
	movdqu XMMWORD PTR [esp+1216], xmm0
	movdqu XMMWORD PTR [esp+1232], xmm0
	movdqu XMMWORD PTR [esp+1248], xmm0
	movdqu XMMWORD PTR [esp+1264], xmm0
	movdqu XMMWORD PTR [esp+1280], xmm0
	movdqu XMMWORD PTR [esp+1296], xmm0
	movdqu XMMWORD PTR [esp+1312], xmm0
	movdqu XMMWORD PTR [esp+1328], xmm0
	movdqu XMMWORD PTR [esp+1344], xmm0
	movdqu XMMWORD PTR [esp+1360], xmm0
	movdqu XMMWORD PTR [esp+1376], xmm0
	movdqu XMMWORD PTR [esp+1392], xmm0
	mov DWORD PTR [esp+1408], ecx
	mov DWORD PTR [esp+1412], ecx
	mov DWORD PTR [esp+1416], ecx
	lea esp, [esp+1420]
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

vg_sha384_digest:
	lea esp, [esp-564]
	mov eax, DWORD PTR [esp+568]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+572]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+576]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov edi, ebp
	add edi, 288
	push edi
	call {vg_sha384_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 480
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, 0
20:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+480]
	mov eax, esi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, 48
	jne 20b
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
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
	lea esp, [esp+564]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-612]
	movdqu XMMWORD PTR [esp], xmm0
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
	mov DWORD PTR [esp+608], ecx
	lea esp, [esp+612]
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

vg_sha512_digest:
	lea esp, [esp-564]
	mov eax, DWORD PTR [esp+568]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+572]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+576]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov edi, ebp
	add edi, 288
	push edi
	call {vg_sha512_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 480
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, 0
20:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+480]
	mov eax, esi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, 64
	jne 20b
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
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
	lea esp, [esp+564]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-612]
	movdqu XMMWORD PTR [esp], xmm0
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
	mov DWORD PTR [esp+608], ecx
	lea esp, [esp+612]
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

vg_sha512_224_digest:
	lea esp, [esp-564]
	mov eax, DWORD PTR [esp+568]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+572]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+576]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov edi, ebp
	add edi, 288
	push edi
	call {vg_sha512_224_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 480
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, 0
20:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+480]
	mov eax, esi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, 28
	jne 20b
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
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
	lea esp, [esp+564]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-612]
	movdqu XMMWORD PTR [esp], xmm0
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
	mov DWORD PTR [esp+608], ecx
	lea esp, [esp+612]
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

vg_sha512_256_digest:
	lea esp, [esp-564]
	mov eax, DWORD PTR [esp+568]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+572]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+576]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov edi, ebp
	add edi, 288
	push edi
	call {vg_sha512_256_init_core}
	pop eax
	mov eax, 0
	mov esi, 0
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha512_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 0
	mov edx, ebp
	add edx, 480
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+12]
	mov ecx, 0
20:
	mov eax, ebp
	add eax, ecx
	movzx edx, BYTE PTR [eax+480]
	mov eax, esi
	add eax, ecx
	mov BYTE PTR [eax], dl
	add ecx, 1
	cmp ecx, 32
	jne 20b
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
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
	lea esp, [esp+564]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-612]
	movdqu XMMWORD PTR [esp], xmm0
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
	mov DWORD PTR [esp+608], ecx
	lea esp, [esp+612]
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
