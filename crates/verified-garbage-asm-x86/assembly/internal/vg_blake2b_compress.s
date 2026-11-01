// The functions of `src/internal/vg_blake2b_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
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
