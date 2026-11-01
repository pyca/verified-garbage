// The functions of `src/internal/vg_sha256_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+96], ebx
	mov DWORD PTR [eax+100], esi
	mov DWORD PTR [eax+104], edi
	mov DWORD PTR [eax+108], ebp
	mov esi, eax
	mov edi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	test ebp, ebp
	je 20f
22:
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [eax]
	mov DWORD PTR [esi+64], ebx
	mov ebx, DWORD PTR [eax+4]
	mov DWORD PTR [esi+68], ebx
	mov ebx, DWORD PTR [eax+8]
	mov DWORD PTR [esi+72], ebx
	mov ebx, DWORD PTR [eax+12]
	mov DWORD PTR [esi+76], ebx
	mov ebx, DWORD PTR [eax+16]
	mov DWORD PTR [esi+80], ebx
	mov ebx, DWORD PTR [eax+20]
	mov DWORD PTR [esi+84], ebx
	mov ebx, DWORD PTR [eax+24]
	mov DWORD PTR [esi+88], ebx
	mov ebx, DWORD PTR [eax+28]
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [edi]
	bswap eax
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, 1116352408
	add ecx, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [edi+4]
	bswap eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, 1899447441
	add ecx, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [edi+8]
	bswap eax
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, -1245643825
	add ecx, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [edi+12]
	bswap eax
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, -373957723
	add ecx, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [edi+16]
	bswap eax
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, 961987163
	add ecx, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [edi+20]
	bswap eax
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, 1508970993
	add ecx, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [edi+24]
	bswap eax
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, -1841331548
	add ecx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [edi+28]
	bswap eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, -1424204075
	add ecx, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [edi+32]
	bswap eax
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, -670586216
	add ecx, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [edi+36]
	bswap eax
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, 310598401
	add ecx, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [edi+40]
	bswap eax
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, 607225278
	add ecx, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [edi+44]
	bswap eax
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, 1426881987
	add ecx, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [edi+48]
	bswap eax
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, 1925078388
	add ecx, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [edi+52]
	bswap eax
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, -2132889090
	add ecx, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [edi+56]
	bswap eax
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, -1680079193
	add ecx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [edi+60]
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, -1046744716
	add ecx, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+56]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+36]
	mov eax, DWORD PTR [esi+4]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi]
	mov DWORD PTR [esi], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, -459576895
	add ecx, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [esi+60]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+40]
	mov eax, DWORD PTR [esi+8]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+4]
	mov DWORD PTR [esi+4], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, -272742522
	add ecx, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [esi]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+44]
	mov eax, DWORD PTR [esi+12]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+8]
	mov DWORD PTR [esi+8], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, 264347078
	add ecx, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [esi+4]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+48]
	mov eax, DWORD PTR [esi+16]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+12]
	mov DWORD PTR [esi+12], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, 604807628
	add ecx, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [esi+8]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+52]
	mov eax, DWORD PTR [esi+20]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+16]
	mov DWORD PTR [esi+16], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, 770255983
	add ecx, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+12]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+24]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+20]
	mov DWORD PTR [esi+20], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, 1249150122
	add ecx, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+16]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+60]
	mov eax, DWORD PTR [esi+28]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+24]
	mov DWORD PTR [esi+24], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, 1555081692
	add ecx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+20]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi+32]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+28]
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, 1996064986
	add ecx, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+24]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [esi+36]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+32]
	mov DWORD PTR [esi+32], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, -1740746414
	add ecx, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [esi+28]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+8]
	mov eax, DWORD PTR [esi+40]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+36]
	mov DWORD PTR [esi+36], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, -1473132947
	add ecx, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [esi+32]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+12]
	mov eax, DWORD PTR [esi+44]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+40]
	mov DWORD PTR [esi+40], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, -1341970488
	add ecx, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [esi+36]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+16]
	mov eax, DWORD PTR [esi+48]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+44]
	mov DWORD PTR [esi+44], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, -1084653625
	add ecx, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [esi+40]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+20]
	mov eax, DWORD PTR [esi+52]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+48], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, -958395405
	add ecx, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+44]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+24]
	mov eax, DWORD PTR [esi+56]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+52]
	mov DWORD PTR [esi+52], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, -710438585
	add ecx, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+48]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+28]
	mov eax, DWORD PTR [esi+60]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+56]
	mov DWORD PTR [esi+56], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, 113926993
	add ecx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+52]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+32]
	mov eax, DWORD PTR [esi]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+60]
	mov DWORD PTR [esi+60], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, 338241895
	add ecx, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+56]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+36]
	mov eax, DWORD PTR [esi+4]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi]
	mov DWORD PTR [esi], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, 666307205
	add ecx, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [esi+60]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+40]
	mov eax, DWORD PTR [esi+8]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+4]
	mov DWORD PTR [esi+4], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, 773529912
	add ecx, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [esi]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+44]
	mov eax, DWORD PTR [esi+12]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+8]
	mov DWORD PTR [esi+8], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, 1294757372
	add ecx, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [esi+4]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+48]
	mov eax, DWORD PTR [esi+16]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+12]
	mov DWORD PTR [esi+12], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, 1396182291
	add ecx, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [esi+8]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+52]
	mov eax, DWORD PTR [esi+20]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+16]
	mov DWORD PTR [esi+16], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, 1695183700
	add ecx, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+12]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+24]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+20]
	mov DWORD PTR [esi+20], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, 1986661051
	add ecx, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+16]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+60]
	mov eax, DWORD PTR [esi+28]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+24]
	mov DWORD PTR [esi+24], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, -2117940946
	add ecx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+20]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi+32]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+28]
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, -1838011259
	add ecx, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+24]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [esi+36]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+32]
	mov DWORD PTR [esi+32], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, -1564481375
	add ecx, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [esi+28]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+8]
	mov eax, DWORD PTR [esi+40]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+36]
	mov DWORD PTR [esi+36], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, -1474664885
	add ecx, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [esi+32]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+12]
	mov eax, DWORD PTR [esi+44]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+40]
	mov DWORD PTR [esi+40], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, -1035236496
	add ecx, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [esi+36]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+16]
	mov eax, DWORD PTR [esi+48]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+44]
	mov DWORD PTR [esi+44], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, -949202525
	add ecx, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [esi+40]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+20]
	mov eax, DWORD PTR [esi+52]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+48], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, -778901479
	add ecx, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+44]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+24]
	mov eax, DWORD PTR [esi+56]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+52]
	mov DWORD PTR [esi+52], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, -694614492
	add ecx, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+48]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+28]
	mov eax, DWORD PTR [esi+60]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+56]
	mov DWORD PTR [esi+56], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, -200395387
	add ecx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+52]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+32]
	mov eax, DWORD PTR [esi]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+60]
	mov DWORD PTR [esi+60], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, 275423344
	add ecx, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+56]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+36]
	mov eax, DWORD PTR [esi+4]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi]
	mov DWORD PTR [esi], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, 430227734
	add ecx, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [esi+60]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+40]
	mov eax, DWORD PTR [esi+8]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+4]
	mov DWORD PTR [esi+4], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, 506948616
	add ecx, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [esi]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+44]
	mov eax, DWORD PTR [esi+12]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+8]
	mov DWORD PTR [esi+8], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, 659060556
	add ecx, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [esi+4]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+48]
	mov eax, DWORD PTR [esi+16]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+12]
	mov DWORD PTR [esi+12], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, 883997877
	add ecx, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [esi+8]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+52]
	mov eax, DWORD PTR [esi+20]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+16]
	mov DWORD PTR [esi+16], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, 958139571
	add ecx, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+12]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+56]
	mov eax, DWORD PTR [esi+24]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+20]
	mov DWORD PTR [esi+20], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, 1322822218
	add ecx, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+16]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+60]
	mov eax, DWORD PTR [esi+28]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+24]
	mov DWORD PTR [esi+24], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, 1537002063
	add ecx, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+20]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi]
	mov eax, DWORD PTR [esi+32]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+28]
	mov DWORD PTR [esi+28], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, 1747873779
	add ecx, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+24]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+4]
	mov eax, DWORD PTR [esi+36]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+32]
	mov DWORD PTR [esi+32], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+92]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [esi+88]
	and ebx, eax
	xor ebx, DWORD PTR [esi+88]
	add ecx, ebx
	add ecx, 1955562222
	add ecx, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+76]
	add ebx, ecx
	mov DWORD PTR [esi+76], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	mov edx, eax
	and edx, DWORD PTR [esi+68]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+92], ecx
	mov eax, DWORD PTR [esi+28]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+8]
	mov eax, DWORD PTR [esi+40]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+36]
	mov DWORD PTR [esi+36], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+88]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [esi+84]
	and ebx, eax
	xor ebx, DWORD PTR [esi+84]
	add ecx, ebx
	add ecx, 2024104815
	add ecx, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+72]
	add ebx, ecx
	mov DWORD PTR [esi+72], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	mov edx, eax
	and edx, DWORD PTR [esi+64]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+88], ecx
	mov eax, DWORD PTR [esi+32]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+12]
	mov eax, DWORD PTR [esi+44]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+40]
	mov DWORD PTR [esi+40], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+84]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [esi+80]
	and ebx, eax
	xor ebx, DWORD PTR [esi+80]
	add ecx, ebx
	add ecx, -2067236844
	add ecx, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi+68]
	add ebx, ecx
	mov DWORD PTR [esi+68], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+92]
	and ebx, DWORD PTR [esi+64]
	mov edx, eax
	and edx, DWORD PTR [esi+92]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+84], ecx
	mov eax, DWORD PTR [esi+36]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+16]
	mov eax, DWORD PTR [esi+48]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+44]
	mov DWORD PTR [esi+44], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+80]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [esi+76]
	and ebx, eax
	xor ebx, DWORD PTR [esi+76]
	add ecx, ebx
	add ecx, -1933114872
	add ecx, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+64]
	add ebx, ecx
	mov DWORD PTR [esi+64], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+88]
	and ebx, DWORD PTR [esi+92]
	mov edx, eax
	and edx, DWORD PTR [esi+88]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+80], ecx
	mov eax, DWORD PTR [esi+40]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+20]
	mov eax, DWORD PTR [esi+52]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+48], ebx
	mov eax, DWORD PTR [esi+64]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [esi+72]
	and ebx, eax
	xor ebx, DWORD PTR [esi+72]
	add ecx, ebx
	add ecx, -1866530822
	add ecx, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+92]
	add ebx, ecx
	mov DWORD PTR [esi+92], ebx
	mov eax, DWORD PTR [esi+80]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+84]
	and ebx, DWORD PTR [esi+88]
	mov edx, eax
	and edx, DWORD PTR [esi+84]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+44]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+24]
	mov eax, DWORD PTR [esi+56]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+52]
	mov DWORD PTR [esi+52], ebx
	mov eax, DWORD PTR [esi+92]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+72]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [esi+68]
	and ebx, eax
	xor ebx, DWORD PTR [esi+68]
	add ecx, ebx
	add ecx, -1538233109
	add ecx, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+88]
	add ebx, ecx
	mov DWORD PTR [esi+88], ebx
	mov eax, DWORD PTR [esi+76]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+80]
	and ebx, DWORD PTR [esi+84]
	mov edx, eax
	and edx, DWORD PTR [esi+80]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+48]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+28]
	mov eax, DWORD PTR [esi+60]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+56]
	mov DWORD PTR [esi+56], ebx
	mov eax, DWORD PTR [esi+88]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+68]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [esi+64]
	and ebx, eax
	xor ebx, DWORD PTR [esi+64]
	add ecx, ebx
	add ecx, -1090935817
	add ecx, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+84]
	add ebx, ecx
	mov DWORD PTR [esi+84], ebx
	mov eax, DWORD PTR [esi+72]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+80]
	mov edx, eax
	and edx, DWORD PTR [esi+76]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+52]
	mov ebx, eax
	ror ebx, 2
	xor ebx, eax
	ror ebx, 17
	shr eax, 10
	xor ebx, eax
	add ebx, DWORD PTR [esi+32]
	mov eax, DWORD PTR [esi]
	mov ecx, eax
	ror ecx, 11
	xor ecx, eax
	ror ecx, 7
	shr eax, 3
	xor ecx, eax
	add ebx, ecx
	add ebx, DWORD PTR [esi+60]
	mov DWORD PTR [esi+60], ebx
	mov eax, DWORD PTR [esi+84]
	mov ebx, eax
	ror ebx, 6
	mov ecx, eax
	ror ecx, 11
	xor ebx, ecx
	ror ecx, 14
	xor ebx, ecx
	mov ecx, DWORD PTR [esi+64]
	add ecx, ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [esi+92]
	and ebx, eax
	xor ebx, DWORD PTR [esi+92]
	add ecx, ebx
	add ecx, -965641998
	add ecx, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+80]
	add ebx, ecx
	mov DWORD PTR [esi+80], ebx
	mov eax, DWORD PTR [esi+68]
	mov ebx, eax
	ror ebx, 2
	mov edx, eax
	ror edx, 13
	xor ebx, edx
	ror edx, 9
	xor ebx, edx
	add ecx, ebx
	mov ebx, eax
	or ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	mov edx, eax
	and edx, DWORD PTR [esi+72]
	or ebx, edx
	add ecx, ebx
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [esi+64]
	add ebx, DWORD PTR [eax]
	mov DWORD PTR [eax], ebx
	mov ebx, DWORD PTR [esi+68]
	add ebx, DWORD PTR [eax+4]
	mov DWORD PTR [eax+4], ebx
	mov ebx, DWORD PTR [esi+72]
	add ebx, DWORD PTR [eax+8]
	mov DWORD PTR [eax+8], ebx
	mov ebx, DWORD PTR [esi+76]
	add ebx, DWORD PTR [eax+12]
	mov DWORD PTR [eax+12], ebx
	mov ebx, DWORD PTR [esi+80]
	add ebx, DWORD PTR [eax+16]
	mov DWORD PTR [eax+16], ebx
	mov ebx, DWORD PTR [esi+84]
	add ebx, DWORD PTR [eax+20]
	mov DWORD PTR [eax+20], ebx
	mov ebx, DWORD PTR [esi+88]
	add ebx, DWORD PTR [eax+24]
	mov DWORD PTR [eax+24], ebx
	mov ebx, DWORD PTR [esi+92]
	add ebx, DWORD PTR [eax+28]
	mov DWORD PTR [eax+28], ebx
	add edi, 64
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [esi+96]
	mov edi, DWORD PTR [esi+104]
	mov ebp, DWORD PTR [esi+108]
	mov esi, DWORD PTR [esi+100]
	ret
	.p2align 6
