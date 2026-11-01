// The functions of `src/ecdsa_brainpoolp512r1_sha512.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sha512_sign:
	lea esp, [esp-260]
	mov DWORD PTR [esp+180], ebx
	mov DWORD PTR [esp+184], esi
	mov DWORD PTR [esp+188], edi
	mov DWORD PTR [esp+192], ebp
	mov esi, DWORD PTR [esp+272]
	mov eax, DWORD PTR [esi+60]
	bswap eax
	mov DWORD PTR [esp+256], eax
	sub eax, -1666645911
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esi+56]
	bswap eax
	mov DWORD PTR [esp+252], eax
	sbb eax, -1249405310
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esi+52]
	bswap eax
	mov DWORD PTR [esp+248], eax
	sbb eax, 140368605
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esi+48]
	bswap eax
	mov DWORD PTR [esp+244], eax
	sbb eax, 498193281
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esi+44]
	bswap eax
	mov DWORD PTR [esp+240], eax
	sbb eax, 2141982791
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esi+40]
	bswap eax
	mov DWORD PTR [esp+236], eax
	sbb eax, 1099325721
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esi+36]
	bswap eax
	mov DWORD PTR [esp+232], eax
	sbb eax, 1286153753
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esi+32]
	bswap eax
	mov DWORD PTR [esp+228], eax
	sbb eax, 1430150209
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esi+28]
	bswap eax
	mov DWORD PTR [esp+224], eax
	sbb eax, 1882392688
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esi+24]
	bswap eax
	mov DWORD PTR [esp+220], eax
	sbb eax, -698114870
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esi+20]
	bswap eax
	mov DWORD PTR [esp+216], eax
	sbb eax, -1278619122
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esi+16]
	bswap eax
	mov DWORD PTR [esp+212], eax
	sbb eax, -886010445
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esi+12]
	bswap eax
	mov DWORD PTR [esp+208], eax
	sbb eax, 868875271
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esi+8]
	bswap eax
	mov DWORD PTR [esp+204], eax
	sbb eax, 1070917294
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esi+4]
	bswap eax
	mov DWORD PTR [esp+200], eax
	sbb eax, -605436789
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esi]
	bswap eax
	mov DWORD PTR [esp+196], eax
	sbb eax, -1428316744
	mov DWORD PTR [esp], eax
	sbb edx, edx
	mov eax, DWORD PTR [esp+256]
	mov ecx, DWORD PTR [esp+60]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+256], eax
	mov eax, DWORD PTR [esp+252]
	mov ecx, DWORD PTR [esp+56]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+252], eax
	mov eax, DWORD PTR [esp+248]
	mov ecx, DWORD PTR [esp+52]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+248], eax
	mov eax, DWORD PTR [esp+244]
	mov ecx, DWORD PTR [esp+48]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+244], eax
	mov eax, DWORD PTR [esp+240]
	mov ecx, DWORD PTR [esp+44]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+240], eax
	mov eax, DWORD PTR [esp+236]
	mov ecx, DWORD PTR [esp+40]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+236], eax
	mov eax, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+36]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+232], eax
	mov eax, DWORD PTR [esp+228]
	mov ecx, DWORD PTR [esp+32]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+228], eax
	mov eax, DWORD PTR [esp+224]
	mov ecx, DWORD PTR [esp+28]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+224], eax
	mov eax, DWORD PTR [esp+220]
	mov ecx, DWORD PTR [esp+24]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+220], eax
	mov eax, DWORD PTR [esp+216]
	mov ecx, DWORD PTR [esp+20]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+216], eax
	mov eax, DWORD PTR [esp+212]
	mov ecx, DWORD PTR [esp+16]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+212], eax
	mov eax, DWORD PTR [esp+208]
	mov ecx, DWORD PTR [esp+12]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+208], eax
	mov eax, DWORD PTR [esp+204]
	mov ecx, DWORD PTR [esp+8]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+204], eax
	mov eax, DWORD PTR [esp+200]
	mov ecx, DWORD PTR [esp+4]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+200], eax
	mov eax, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp]
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	bswap eax
	mov DWORD PTR [esp+196], eax
	mov eax, 16843009
	mov ecx, 0
	mov DWORD PTR [esp+64], eax
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+68], eax
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+72], eax
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+76], eax
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+80], eax
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+84], eax
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+88], eax
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+92], eax
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+96], eax
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+100], eax
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+108], eax
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+112], eax
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+120], eax
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+124], eax
	mov DWORD PTR [esp+60], ecx
	mov edi, DWORD PTR [esp+276]
	mov esi, DWORD PTR [esp+268]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 0
	mov BYTE PTR [edi+2320], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2413], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2417], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2421], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2425], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2429], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2433], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2437], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2441], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2445], eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+276]
	add edx, 2256
	mov ecx, 193
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 321
	mov ecx, 0
	mov edi, esp
	add edi, 0
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 192
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	mov esi, DWORD PTR [esp+268]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 1
	mov BYTE PTR [edi+2320], al
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+2321], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+2325], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+2329], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+2333], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+2337], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+2341], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+2345], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+2349], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+2353], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+2357], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+2361], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+2365], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+2369], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+2373], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+2377], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+2381], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [edi+2385], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [edi+2389], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [edi+2393], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [edi+2397], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [edi+2401], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [edi+2405], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [edi+2409], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [edi+2413], eax
	mov eax, DWORD PTR [esp+228]
	mov DWORD PTR [edi+2417], eax
	mov eax, DWORD PTR [esp+232]
	mov DWORD PTR [edi+2421], eax
	mov eax, DWORD PTR [esp+236]
	mov DWORD PTR [edi+2425], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [edi+2429], eax
	mov eax, DWORD PTR [esp+244]
	mov DWORD PTR [edi+2433], eax
	mov eax, DWORD PTR [esp+248]
	mov DWORD PTR [edi+2437], eax
	mov eax, DWORD PTR [esp+252]
	mov DWORD PTR [edi+2441], eax
	mov eax, DWORD PTR [esp+256]
	mov DWORD PTR [edi+2445], eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+276]
	add edx, 2256
	mov ecx, 193
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 321
	mov ecx, 0
	mov edi, esp
	add edi, 0
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 192
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 128
	mov DWORD PTR [esp+176], eax
20:
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 192
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+264]
	mov esi, DWORD PTR [esp+268]
	mov edx, DWORD PTR [esp+272]
	mov ecx, esp
	add ecx, 64
	mov ebp, DWORD PTR [esp+276]
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_ecdsa_brainpoolp512r1_sign}
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	pop ecx
	mov ecx, DWORD PTR [esp+176]
	sub ecx, 1
	mov DWORD PTR [esp+176], ecx
	cmp eax, 1
	sbb edx, edx
	and edx, ecx
	test edx, edx
	jne 21f
	mov edx, 0
	test edx, edx
	jmp 22f
21:
	mov edi, DWORD PTR [esp+276]
	mov esi, DWORD PTR [esp+268]
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [edi+2256], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [edi+2260], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [edi+2264], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [edi+2268], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [edi+2272], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [edi+2276], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [edi+2280], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [edi+2284], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [edi+2288], eax
	mov eax, DWORD PTR [esp+100]
	mov DWORD PTR [edi+2292], eax
	mov eax, DWORD PTR [esp+104]
	mov DWORD PTR [edi+2296], eax
	mov eax, DWORD PTR [esp+108]
	mov DWORD PTR [edi+2300], eax
	mov eax, DWORD PTR [esp+112]
	mov DWORD PTR [edi+2304], eax
	mov eax, DWORD PTR [esp+116]
	mov DWORD PTR [edi+2308], eax
	mov eax, DWORD PTR [esp+120]
	mov DWORD PTR [edi+2312], eax
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [edi+2316], eax
	mov eax, 0
	mov BYTE PTR [edi+2320], al
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, DWORD PTR [esp+276]
	add edx, 2256
	mov ecx, 65
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 193
	mov ecx, 0
	mov edi, esp
	add edi, 0
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov edx, esp
	add edx, 0
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha512_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+276]
	add edi, 0
	mov esi, 128
	mov eax, 0
	mov edx, esp
	add edx, 64
	mov ecx, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
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
	mov edx, DWORD PTR [esp+276]
	add edx, 0
	mov esi, DWORD PTR [esp+276]
	add esi, 192
	mov eax, 192
	mov ecx, 0
	mov edi, esp
	add edi, 64
	mov ebp, DWORD PTR [esp+276]
	add ebp, 384
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha512_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, 1
	test edx, edx
22:
	jne 20b
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
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov ebx, DWORD PTR [esp+180]
	mov esi, DWORD PTR [esp+184]
	mov edi, DWORD PTR [esp+188]
	mov ebp, DWORD PTR [esp+192]
	lea esp, [esp+260]
	ret
	.p2align 6
