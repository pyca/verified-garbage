// The functions of `src/blake2b.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_compress:
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+288], ebx
	mov DWORD PTR [eax+292], esi
	mov DWORD PTR [eax+296], edi
	mov DWORD PTR [eax+300], ebp
	mov esi, eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [esi+256], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [esi+264], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [esi+268], eax
	mov eax, 0
	mov DWORD PTR [esi+272], eax
	mov DWORD PTR [esi+276], eax
	mov eax, DWORD PTR [esp+24]
	mov ecx, 0
	cmp ecx, eax
	sbb ecx, ecx
	mov DWORD PTR [esi+280], ecx
	mov DWORD PTR [esi+284], ecx
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [esi+260], eax
	test eax, eax
	je 20f
22:
	mov edi, DWORD PTR [esi+256]
	mov eax, DWORD PTR [edi]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+4]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+32]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+36]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+40]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+44]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+52]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+56]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+60]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+64]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+68]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+72]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+76]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+84]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+88]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+92]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+96]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+100]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+104]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+108]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+116]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+120]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+124]
	mov DWORD PTR [esi+124], eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [ecx+32]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [ecx+36]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [ecx+40]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [ecx+44]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [ecx+48]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [ecx+52]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [ecx+56]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [ecx+60]
	mov DWORD PTR [esi+188], eax
	mov eax, -205731576
	mov DWORD PTR [esi+192], eax
	mov eax, 1779033703
	mov DWORD PTR [esi+196], eax
	mov eax, -2067093701
	mov DWORD PTR [esi+200], eax
	mov eax, -1150833019
	mov DWORD PTR [esi+204], eax
	mov eax, -23791573
	mov DWORD PTR [esi+208], eax
	mov eax, 1013904242
	mov DWORD PTR [esi+212], eax
	mov eax, 1595750129
	mov DWORD PTR [esi+216], eax
	mov eax, -1521486534
	mov DWORD PTR [esi+220], eax
	mov eax, -1377402159
	xor eax, DWORD PTR [esi+264]
	mov DWORD PTR [esi+224], eax
	mov eax, 1359893119
	xor eax, DWORD PTR [esi+268]
	mov DWORD PTR [esi+228], eax
	mov eax, 725511199
	xor eax, DWORD PTR [esi+272]
	mov DWORD PTR [esi+232], eax
	mov eax, -1694144372
	xor eax, DWORD PTR [esi+276]
	mov DWORD PTR [esi+236], eax
	mov eax, -79577749
	xor eax, DWORD PTR [esi+280]
	mov DWORD PTR [esi+240], eax
	mov eax, 528734635
	xor eax, DWORD PTR [esi+284]
	mov DWORD PTR [esi+244], eax
	mov eax, 327033209
	mov DWORD PTR [esi+248], eax
	mov eax, 1541459225
	mov DWORD PTR [esi+252], eax
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+112]
	adc ebx, DWORD PTR [esi+116]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+80]
	adc ebx, DWORD PTR [esi+84]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+32]
	adc ebx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+64]
	adc ebx, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi+72]
	adc ebx, DWORD PTR [esi+76]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+120]
	adc ebx, DWORD PTR [esi+124]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+104]
	adc ebx, DWORD PTR [esi+108]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+48]
	adc ebx, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+128]
	mov ebx, DWORD PTR [esi+132]
	add eax, DWORD PTR [esi+168]
	adc ebx, DWORD PTR [esi+172]
	add eax, DWORD PTR [esi+8]
	adc ebx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+248]
	mov edx, DWORD PTR [esi+252]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+208]
	mov ebp, DWORD PTR [esi+212]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+248], edx
	mov DWORD PTR [esi+252], ecx
	mov ecx, DWORD PTR [esi+168]
	mov edx, DWORD PTR [esi+172]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+208], edi
	mov DWORD PTR [esi+212], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+96]
	adc ebx, DWORD PTR [esi+100]
	mov edi, DWORD PTR [esi+248]
	mov ebp, DWORD PTR [esi+252]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+128], eax
	mov DWORD PTR [esi+132], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+208]
	mov ebx, DWORD PTR [esi+212]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+248], ebp
	mov DWORD PTR [esi+252], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+208], eax
	mov DWORD PTR [esi+212], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+168], edx
	mov DWORD PTR [esi+172], ecx
	mov eax, DWORD PTR [esi+136]
	mov ebx, DWORD PTR [esi+140]
	add eax, DWORD PTR [esi+176]
	adc ebx, DWORD PTR [esi+180]
	add eax, DWORD PTR [esi]
	adc ebx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+224]
	mov edx, DWORD PTR [esi+228]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+216]
	mov ebp, DWORD PTR [esi+220]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+224], edx
	mov DWORD PTR [esi+228], ecx
	mov ecx, DWORD PTR [esi+176]
	mov edx, DWORD PTR [esi+180]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+216], edi
	mov DWORD PTR [esi+220], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+16]
	adc ebx, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+224]
	mov ebp, DWORD PTR [esi+228]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+136], eax
	mov DWORD PTR [esi+140], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+216]
	mov ebx, DWORD PTR [esi+220]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+224], ebp
	mov DWORD PTR [esi+228], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+216], eax
	mov DWORD PTR [esi+220], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+176], edx
	mov DWORD PTR [esi+180], ecx
	mov eax, DWORD PTR [esi+144]
	mov ebx, DWORD PTR [esi+148]
	add eax, DWORD PTR [esi+184]
	adc ebx, DWORD PTR [esi+188]
	add eax, DWORD PTR [esi+88]
	adc ebx, DWORD PTR [esi+92]
	mov ecx, DWORD PTR [esi+232]
	mov edx, DWORD PTR [esi+236]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+192]
	mov ebp, DWORD PTR [esi+196]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+232], edx
	mov DWORD PTR [esi+236], ecx
	mov ecx, DWORD PTR [esi+184]
	mov edx, DWORD PTR [esi+188]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+192], edi
	mov DWORD PTR [esi+196], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+56]
	adc ebx, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+232]
	mov ebp, DWORD PTR [esi+236]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+144], eax
	mov DWORD PTR [esi+148], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+192]
	mov ebx, DWORD PTR [esi+196]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+232], ebp
	mov DWORD PTR [esi+236], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+192], eax
	mov DWORD PTR [esi+196], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+184], edx
	mov DWORD PTR [esi+188], ecx
	mov eax, DWORD PTR [esi+152]
	mov ebx, DWORD PTR [esi+156]
	add eax, DWORD PTR [esi+160]
	adc ebx, DWORD PTR [esi+164]
	add eax, DWORD PTR [esi+40]
	adc ebx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+240]
	mov edx, DWORD PTR [esi+244]
	xor ecx, eax
	xor edx, ebx
	mov edi, DWORD PTR [esi+200]
	mov ebp, DWORD PTR [esi+204]
	add edi, edx
	adc ebp, ecx
	mov DWORD PTR [esi+240], edx
	mov DWORD PTR [esi+244], ecx
	mov ecx, DWORD PTR [esi+160]
	mov edx, DWORD PTR [esi+164]
	xor ecx, edi
	xor edx, ebp
	mov DWORD PTR [esi+200], edi
	mov DWORD PTR [esi+204], ebp
	ror ecx, 24
	ror edx, 24
	mov edi, ecx
	xor edi, edx
	and edi, 255
	xor ecx, edi
	xor edx, edi
	add eax, edx
	adc ebx, ecx
	add eax, DWORD PTR [esi+24]
	adc ebx, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+240]
	mov ebp, DWORD PTR [esi+244]
	xor edi, eax
	xor ebp, ebx
	mov DWORD PTR [esi+152], eax
	mov DWORD PTR [esi+156], ebx
	ror edi, 16
	ror ebp, 16
	mov eax, edi
	xor eax, ebp
	and eax, 65535
	xor edi, eax
	xor ebp, eax
	mov eax, DWORD PTR [esi+200]
	mov ebx, DWORD PTR [esi+204]
	add eax, ebp
	adc ebx, edi
	mov DWORD PTR [esi+240], ebp
	mov DWORD PTR [esi+244], edi
	xor edx, eax
	xor ecx, ebx
	mov DWORD PTR [esi+200], eax
	mov DWORD PTR [esi+204], ebx
	ror ecx, 31
	ror edx, 31
	mov eax, ecx
	xor eax, edx
	and eax, 1
	xor ecx, eax
	xor edx, eax
	mov DWORD PTR [esi+160], edx
	mov DWORD PTR [esi+164], ecx
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	xor eax, DWORD PTR [esi+128]
	xor eax, DWORD PTR [esi+192]
	mov DWORD PTR [ecx], eax
	mov eax, DWORD PTR [ecx+4]
	xor eax, DWORD PTR [esi+132]
	xor eax, DWORD PTR [esi+196]
	mov DWORD PTR [ecx+4], eax
	mov eax, DWORD PTR [ecx+8]
	xor eax, DWORD PTR [esi+136]
	xor eax, DWORD PTR [esi+200]
	mov DWORD PTR [ecx+8], eax
	mov eax, DWORD PTR [ecx+12]
	xor eax, DWORD PTR [esi+140]
	xor eax, DWORD PTR [esi+204]
	mov DWORD PTR [ecx+12], eax
	mov eax, DWORD PTR [ecx+16]
	xor eax, DWORD PTR [esi+144]
	xor eax, DWORD PTR [esi+208]
	mov DWORD PTR [ecx+16], eax
	mov eax, DWORD PTR [ecx+20]
	xor eax, DWORD PTR [esi+148]
	xor eax, DWORD PTR [esi+212]
	mov DWORD PTR [ecx+20], eax
	mov eax, DWORD PTR [ecx+24]
	xor eax, DWORD PTR [esi+152]
	xor eax, DWORD PTR [esi+216]
	mov DWORD PTR [ecx+24], eax
	mov eax, DWORD PTR [ecx+28]
	xor eax, DWORD PTR [esi+156]
	xor eax, DWORD PTR [esi+220]
	mov DWORD PTR [ecx+28], eax
	mov eax, DWORD PTR [ecx+32]
	xor eax, DWORD PTR [esi+160]
	xor eax, DWORD PTR [esi+224]
	mov DWORD PTR [ecx+32], eax
	mov eax, DWORD PTR [ecx+36]
	xor eax, DWORD PTR [esi+164]
	xor eax, DWORD PTR [esi+228]
	mov DWORD PTR [ecx+36], eax
	mov eax, DWORD PTR [ecx+40]
	xor eax, DWORD PTR [esi+168]
	xor eax, DWORD PTR [esi+232]
	mov DWORD PTR [ecx+40], eax
	mov eax, DWORD PTR [ecx+44]
	xor eax, DWORD PTR [esi+172]
	xor eax, DWORD PTR [esi+236]
	mov DWORD PTR [ecx+44], eax
	mov eax, DWORD PTR [ecx+48]
	xor eax, DWORD PTR [esi+176]
	xor eax, DWORD PTR [esi+240]
	mov DWORD PTR [ecx+48], eax
	mov eax, DWORD PTR [ecx+52]
	xor eax, DWORD PTR [esi+180]
	xor eax, DWORD PTR [esi+244]
	mov DWORD PTR [ecx+52], eax
	mov eax, DWORD PTR [ecx+56]
	xor eax, DWORD PTR [esi+184]
	xor eax, DWORD PTR [esi+248]
	mov DWORD PTR [ecx+56], eax
	mov eax, DWORD PTR [ecx+60]
	xor eax, DWORD PTR [esi+188]
	xor eax, DWORD PTR [esi+252]
	mov DWORD PTR [ecx+60], eax
	mov eax, DWORD PTR [esi+256]
	add eax, 128
	mov DWORD PTR [esi+256], eax
	mov eax, DWORD PTR [esi+264]
	add eax, 128
	mov DWORD PTR [esi+264], eax
	mov eax, DWORD PTR [esi+268]
	adc eax, 0
	mov DWORD PTR [esi+268], eax
	mov eax, DWORD PTR [esi+272]
	adc eax, 0
	mov DWORD PTR [esi+272], eax
	mov eax, DWORD PTR [esi+276]
	adc eax, 0
	mov DWORD PTR [esi+276], eax
	mov eax, DWORD PTR [esi+260]
	sub eax, 1
	mov DWORD PTR [esi+260], eax
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esi+288]
	mov edi, DWORD PTR [esi+296]
	mov ebp, DWORD PTR [esi+300]
	mov esi, DWORD PTR [esi+292]
	ret
	.p2align 6

vg_blake2b_init:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+16]
	test ecx, ecx
	je 20f
	mov edx, 0
	mov DWORD PTR [eax+64], edx
	mov DWORD PTR [eax+68], edx
	mov DWORD PTR [eax+72], edx
	mov DWORD PTR [eax+76], edx
	mov DWORD PTR [eax+80], edx
	mov DWORD PTR [eax+84], edx
	mov DWORD PTR [eax+88], edx
	mov DWORD PTR [eax+92], edx
	mov DWORD PTR [eax+96], edx
	mov DWORD PTR [eax+100], edx
	mov DWORD PTR [eax+104], edx
	mov DWORD PTR [eax+108], edx
	mov DWORD PTR [eax+112], edx
	mov DWORD PTR [eax+116], edx
	mov DWORD PTR [eax+120], edx
	mov DWORD PTR [eax+124], edx
	mov DWORD PTR [eax+128], edx
	mov DWORD PTR [eax+132], edx
	mov DWORD PTR [eax+136], edx
	mov DWORD PTR [eax+140], edx
	mov DWORD PTR [eax+144], edx
	mov DWORD PTR [eax+148], edx
	mov DWORD PTR [eax+152], edx
	mov DWORD PTR [eax+156], edx
	mov DWORD PTR [eax+160], edx
	mov DWORD PTR [eax+164], edx
	mov DWORD PTR [eax+168], edx
	mov DWORD PTR [eax+172], edx
	mov DWORD PTR [eax+176], edx
	mov DWORD PTR [eax+180], edx
	mov DWORD PTR [eax+184], edx
	mov DWORD PTR [eax+188], edx
	mov DWORD PTR [eax], ebx
	mov edx, DWORD PTR [esp+12]
22:
	movzx ebx, BYTE PTR [edx]
	mov BYTE PTR [eax+64], bl
	add edx, 1
	add eax, 1
	sub ecx, 1
	jne 22b
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [eax]
	jmp 21f
20:
21:
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
	mov ecx, DWORD PTR [eax]
	xor ecx, 16842752
	mov edx, DWORD PTR [esp+16]
	ror edx, 24
	xor ecx, edx
	xor ecx, DWORD PTR [esp+8]
	mov DWORD PTR [eax], ecx
	ret
	.p2align 6

vg_blake2b_update:
	lea esp, [esp-604]
	mov eax, DWORD PTR [esp+608]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+620]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+624]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+528], eax
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+532], ecx
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	test edi, edi
	je 22f
	test eax, eax
	je 24f
	mov ecx, 128
	sub ecx, eax
	cmp edi, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, edi
27:
	sub edi, ecx
	mov edx, ebx
	add edx, eax
	mov eax, DWORD PTR [ebp+528]
	add eax, ecx
	mov DWORD PTR [ebp+528], eax
	mov eax, DWORD PTR [ebp+532]
	adc eax, 0
	mov DWORD PTR [ebp+532], eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	test edi, edi
	je 211f
	mov DWORD PTR [ebp+536], esi
	mov DWORD PTR [ebp+540], edi
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebp+536]
	mov edi, DWORD PTR [ebp+540]
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test edi, edi
	je 213f
	mov eax, edi
	sub eax, 1
	mov ecx, eax
	and ecx, 127
	sub eax, ecx
	je 215f
	mov DWORD PTR [ebp+540], edi
	mov DWORD PTR [ebp+544], eax
	mov edi, eax
	shr edi, 7
	mov ecx, DWORD PTR [ebp+528]
	add ecx, 128
	mov edx, DWORD PTR [ebp+532]
	adc edx, 0
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+544]
	add esi, eax
	mov edi, DWORD PTR [ebp+540]
	sub edi, eax
	jmp 216f
215:
216:
	mov ecx, edi
	mov edx, ebx
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	lea esp, [esp+604]
	ret
	.p2align 6

vg_blake2b_finalize:
	lea esp, [esp-600]
	mov eax, DWORD PTR [esp+604]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+608]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+612]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+616]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov edx, ebx
	add edx, eax
	mov ecx, 128
	sub ecx, eax
	mov eax, 0
	je 22f
24:
	mov BYTE PTR [edx+64], al
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+32]
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+36]
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+40]
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+44]
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+48]
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+52]
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+56]
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+60]
	mov DWORD PTR [eax+60], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	lea esp, [esp+600]
	ret
	.p2align 6

vg_blake2b_update_scratch:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+528], eax
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+532], ecx
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	test edi, edi
	je 22f
	test eax, eax
	je 24f
	mov ecx, 128
	sub ecx, eax
	cmp edi, ecx
	jb 26f
	jmp 27f
26:
	mov ecx, edi
27:
	sub edi, ecx
	mov edx, ebx
	add edx, eax
	mov eax, DWORD PTR [ebp+528]
	add eax, ecx
	mov DWORD PTR [ebp+528], eax
	mov eax, DWORD PTR [ebp+532]
	adc eax, 0
	mov DWORD PTR [ebp+532], eax
	test ecx, ecx
	je 28f
210:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 210b
	jmp 29f
28:
29:
	test edi, edi
	je 211f
	mov DWORD PTR [ebp+536], esi
	mov DWORD PTR [ebp+540], edi
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov ecx, DWORD PTR [ebp+528]
	mov edx, DWORD PTR [ebp+532]
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [ebp+536]
	mov edi, DWORD PTR [ebp+540]
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test edi, edi
	je 213f
	mov eax, edi
	sub eax, 1
	mov ecx, eax
	and ecx, 127
	sub eax, ecx
	je 215f
	mov DWORD PTR [ebp+540], edi
	mov DWORD PTR [ebp+544], eax
	mov edi, eax
	shr edi, 7
	mov ecx, DWORD PTR [ebp+528]
	add ecx, 128
	mov edx, DWORD PTR [ebp+532]
	adc edx, 0
	mov eax, 0
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+544]
	add esi, eax
	mov edi, DWORD PTR [ebp+540]
	sub edi, eax
	jmp 216f
215:
216:
	mov ecx, edi
	mov edx, ebx
217:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edx+64], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	ret
	.p2align 6

vg_blake2b_finalize_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+512], ebx
	mov DWORD PTR [eax+516], esi
	mov DWORD PTR [eax+520], edi
	mov DWORD PTR [eax+524], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 127
	add eax, 1
	jmp 21f
20:
	mov eax, 0
21:
	mov edx, ebx
	add edx, eax
	mov ecx, 128
	sub ecx, eax
	mov eax, 0
	je 22f
24:
	mov BYTE PTR [edx+64], al
	add edx, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov esi, ebx
	add esi, 64
	mov edi, 1
	mov eax, 1
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	push ebp
	push eax
	push edx
	push ecx
	push edi
	push esi
	push ebx
	call {vg_blake2b_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx]
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [ebx+20]
	mov DWORD PTR [eax+20], ecx
	mov ecx, DWORD PTR [ebx+24]
	mov DWORD PTR [eax+24], ecx
	mov ecx, DWORD PTR [ebx+28]
	mov DWORD PTR [eax+28], ecx
	mov ecx, DWORD PTR [ebx+32]
	mov DWORD PTR [eax+32], ecx
	mov ecx, DWORD PTR [ebx+36]
	mov DWORD PTR [eax+36], ecx
	mov ecx, DWORD PTR [ebx+40]
	mov DWORD PTR [eax+40], ecx
	mov ecx, DWORD PTR [ebx+44]
	mov DWORD PTR [eax+44], ecx
	mov ecx, DWORD PTR [ebx+48]
	mov DWORD PTR [eax+48], ecx
	mov ecx, DWORD PTR [ebx+52]
	mov DWORD PTR [eax+52], ecx
	mov ecx, DWORD PTR [ebx+56]
	mov DWORD PTR [eax+56], ecx
	mov ecx, DWORD PTR [ebx+60]
	mov DWORD PTR [eax+60], ecx
	mov eax, ebp
	mov ebx, DWORD PTR [eax+512]
	mov esi, DWORD PTR [eax+516]
	mov edi, DWORD PTR [eax+520]
	mov ebp, DWORD PTR [eax+524]
	ret
	.p2align 6
