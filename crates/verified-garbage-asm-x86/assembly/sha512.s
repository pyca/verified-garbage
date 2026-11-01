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
	ret
	.p2align 6
