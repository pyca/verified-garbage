// The functions of `src/internal/vg_sm3_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_compress:
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
	mov eax, DWORD PTR [edi]
	bswap eax
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+4]
	bswap eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+8]
	bswap eax
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+12]
	bswap eax
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+16]
	bswap eax
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+20]
	bswap eax
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+24]
	bswap eax
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+28]
	bswap eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+32]
	bswap eax
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+36]
	bswap eax
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+40]
	bswap eax
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+44]
	bswap eax
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+48]
	bswap eax
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+52]
	bswap eax
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+56]
	bswap eax
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+60]
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov DWORD PTR [esi+84], edi
	mov DWORD PTR [esi+88], ebp
	mov edi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+20]
	mov ebp, DWORD PTR [esi]
	xor ebp, DWORD PTR [esi+16]
	add ebp, DWORD PTR [esi+64]
	mov edi, eax
	xor edi, ebx
	xor edi, DWORD PTR [esi+68]
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 2043430169
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi]
	xor ebx, ecx
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+4]
	xor ebx, DWORD PTR [esi+20]
	add ebx, DWORD PTR [esi+68]
	mov edx, ebp
	xor edx, eax
	xor edx, DWORD PTR [esi+64]
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -208106958
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+4]
	xor eax, edi
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+24]
	add eax, DWORD PTR [esi+64]
	mov ecx, ebx
	xor ecx, ebp
	xor ecx, DWORD PTR [esi+68]
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -416213915
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+8]
	xor ebp, edx
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+12]
	xor ebp, DWORD PTR [esi+28]
	add ebp, DWORD PTR [esi+68]
	mov edi, eax
	xor edi, ebx
	xor edi, DWORD PTR [esi+64]
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -832427829
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+12]
	xor ebx, ecx
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+16]
	xor ebx, DWORD PTR [esi+32]
	add ebx, DWORD PTR [esi+64]
	mov edx, ebp
	xor edx, eax
	xor edx, DWORD PTR [esi+68]
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -1664855657
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+16]
	xor eax, edi
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+36]
	add eax, DWORD PTR [esi+68]
	mov ecx, ebx
	xor ecx, ebp
	xor ecx, DWORD PTR [esi+64]
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 965255983
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+20]
	xor ebp, edx
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+24]
	xor ebp, DWORD PTR [esi+40]
	add ebp, DWORD PTR [esi+64]
	mov edi, eax
	xor edi, ebx
	xor edi, DWORD PTR [esi+68]
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 1930511966
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+24]
	xor ebx, ecx
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+28]
	xor ebx, DWORD PTR [esi+44]
	add ebx, DWORD PTR [esi+68]
	mov edx, ebp
	xor edx, eax
	xor edx, DWORD PTR [esi+64]
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -433943364
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+28]
	xor eax, edi
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+48]
	add eax, DWORD PTR [esi+64]
	mov ecx, ebx
	xor ecx, ebp
	xor ecx, DWORD PTR [esi+68]
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -867886727
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+32]
	xor ebp, edx
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi]
	xor ebp, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+52]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+12]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+40]
	mov DWORD PTR [esi], ebp
	mov ebp, DWORD PTR [esi+36]
	xor ebp, DWORD PTR [esi+52]
	add ebp, DWORD PTR [esi+68]
	mov edi, eax
	xor edi, ebx
	xor edi, DWORD PTR [esi+64]
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1735773453
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+36]
	xor ebx, ecx
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+4]
	xor ebx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+56]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+16]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [esi+40]
	xor ebx, DWORD PTR [esi+56]
	add ebx, DWORD PTR [esi+64]
	mov edx, ebp
	xor edx, eax
	xor edx, DWORD PTR [esi+68]
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 823420391
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+40]
	xor eax, edi
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+60]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+20]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+60]
	add eax, DWORD PTR [esi+68]
	mov ecx, ebx
	xor ecx, ebp
	xor ecx, DWORD PTR [esi+64]
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 1646840782
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+44]
	xor ebp, edx
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+12]
	xor ebp, DWORD PTR [esi+40]
	mov edi, DWORD PTR [esi]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+24]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], ebp
	mov ebp, DWORD PTR [esi+48]
	xor ebp, DWORD PTR [esi]
	add ebp, DWORD PTR [esi+64]
	mov edi, eax
	xor edi, ebx
	xor edi, DWORD PTR [esi+68]
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1001285732
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+48]
	xor ebx, ecx
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+16]
	xor ebx, DWORD PTR [esi+44]
	mov edx, DWORD PTR [esi+4]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+28]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+56]
	mov DWORD PTR [esi+16], ebx
	mov ebx, DWORD PTR [esi+52]
	xor ebx, DWORD PTR [esi+4]
	add ebx, DWORD PTR [esi+68]
	mov edx, ebp
	xor edx, eax
	xor edx, DWORD PTR [esi+64]
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -2002571463
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+52]
	xor eax, edi
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+8]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+32]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+64]
	mov ecx, ebx
	xor ecx, ebp
	xor ecx, DWORD PTR [esi+68]
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 289824371
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+56]
	xor ebp, edx
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+24]
	xor ebp, DWORD PTR [esi+52]
	mov edi, DWORD PTR [esi+12]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+36]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi]
	mov DWORD PTR [esi+24], ebp
	mov ebp, DWORD PTR [esi+60]
	xor ebp, DWORD PTR [esi+12]
	add ebp, DWORD PTR [esi+68]
	mov edi, eax
	xor edi, ebx
	xor edi, DWORD PTR [esi+64]
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 579648742
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+60]
	xor ebx, ecx
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+28]
	xor ebx, DWORD PTR [esi+56]
	mov edx, DWORD PTR [esi+16]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+40]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+4]
	mov DWORD PTR [esi+28], ebx
	mov ebx, DWORD PTR [esi]
	xor ebx, DWORD PTR [esi+16]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -1651869049
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+20]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+44]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+20]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 991229199
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+4]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+36]
	xor ebp, DWORD PTR [esi]
	mov edi, DWORD PTR [esi+24]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+48]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+12]
	mov DWORD PTR [esi+36], ebp
	mov ebp, DWORD PTR [esi+8]
	xor ebp, DWORD PTR [esi+24]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 1982458398
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+8]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+40]
	xor ebx, DWORD PTR [esi+4]
	mov edx, DWORD PTR [esi+28]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+52]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+16]
	mov DWORD PTR [esi+40], ebx
	mov ebx, DWORD PTR [esi+12]
	xor ebx, DWORD PTR [esi+28]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -330050500
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+12]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [esi+32]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+56]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+32]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -660100999
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+16]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+48]
	xor ebp, DWORD PTR [esi+12]
	mov edi, DWORD PTR [esi+36]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+60]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+24]
	mov DWORD PTR [esi+48], ebp
	mov ebp, DWORD PTR [esi+20]
	xor ebp, DWORD PTR [esi+36]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1320201997
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+20]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+52]
	xor ebx, DWORD PTR [esi+16]
	mov edx, DWORD PTR [esi+40]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+28]
	mov DWORD PTR [esi+52], ebx
	mov ebx, DWORD PTR [esi+24]
	xor ebx, DWORD PTR [esi+40]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 1654563303
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+24]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+44]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+4]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+44]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -985840690
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+28]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+60]
	xor ebp, DWORD PTR [esi+24]
	mov edi, DWORD PTR [esi+48]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+8]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+36]
	mov DWORD PTR [esi+60], ebp
	mov ebp, DWORD PTR [esi+32]
	xor ebp, DWORD PTR [esi+48]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1971681379
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+32]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi]
	xor ebx, DWORD PTR [esi+28]
	mov edx, DWORD PTR [esi+52]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+12]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+40]
	mov DWORD PTR [esi], ebx
	mov ebx, DWORD PTR [esi+36]
	xor ebx, DWORD PTR [esi+52]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 351604539
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+36]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+32]
	mov ecx, DWORD PTR [esi+56]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+16]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+56]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 703209078
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+40]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+8]
	xor ebp, DWORD PTR [esi+36]
	mov edi, DWORD PTR [esi+60]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+20]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], ebp
	mov ebp, DWORD PTR [esi+44]
	xor ebp, DWORD PTR [esi+60]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 1406418156
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+44]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+12]
	xor ebx, DWORD PTR [esi+40]
	mov edx, DWORD PTR [esi]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+24]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], ebx
	mov ebx, DWORD PTR [esi+48]
	xor ebx, DWORD PTR [esi]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -1482130984
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+48]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+4]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+28]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+4]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 1330705329
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+52]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+20]
	xor ebp, DWORD PTR [esi+48]
	mov edi, DWORD PTR [esi+8]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+32]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+60]
	mov DWORD PTR [esi+20], ebp
	mov ebp, DWORD PTR [esi+56]
	xor ebp, DWORD PTR [esi+8]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1633556638
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+56]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+24]
	xor ebx, DWORD PTR [esi+52]
	mov edx, DWORD PTR [esi+12]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+36]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi]
	mov DWORD PTR [esi+24], ebx
	mov ebx, DWORD PTR [esi+60]
	xor ebx, DWORD PTR [esi+12]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 1027854021
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+60]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+16]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+40]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+16]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 2055708042
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+32]
	xor ebp, DWORD PTR [esi+60]
	mov edi, DWORD PTR [esi+20]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+44]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+8]
	mov DWORD PTR [esi+32], ebp
	mov ebp, DWORD PTR [esi+4]
	xor ebp, DWORD PTR [esi+20]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -183551212
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+4]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+36]
	xor ebx, DWORD PTR [esi]
	mov edx, DWORD PTR [esi+24]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+48]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+12]
	mov DWORD PTR [esi+36], ebx
	mov ebx, DWORD PTR [esi+8]
	xor ebx, DWORD PTR [esi+24]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -367102423
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+8]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+28]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+52]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+28]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -734204845
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+12]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+44]
	xor ebp, DWORD PTR [esi+8]
	mov edi, DWORD PTR [esi+32]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+56]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+20]
	mov DWORD PTR [esi+44], ebp
	mov ebp, DWORD PTR [esi+16]
	xor ebp, DWORD PTR [esi+32]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1468409689
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+16]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+48]
	xor ebx, DWORD PTR [esi+12]
	mov edx, DWORD PTR [esi+36]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+60]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+24]
	mov DWORD PTR [esi+48], ebx
	mov ebx, DWORD PTR [esi+20]
	xor ebx, DWORD PTR [esi+36]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 1358147919
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+20]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+40]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+40]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -1578671458
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+24]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+56]
	xor ebp, DWORD PTR [esi+20]
	mov edi, DWORD PTR [esi+44]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+4]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+32]
	mov DWORD PTR [esi+56], ebp
	mov ebp, DWORD PTR [esi+28]
	xor ebp, DWORD PTR [esi+44]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 1137624381
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+28]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+60]
	xor ebx, DWORD PTR [esi+24]
	mov edx, DWORD PTR [esi+48]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+8]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+36]
	mov DWORD PTR [esi+60], ebx
	mov ebx, DWORD PTR [esi+32]
	xor ebx, DWORD PTR [esi+48]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -2019718534
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+32]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+52]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+12]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi+52]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 255530229
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+36]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+4]
	xor ebp, DWORD PTR [esi+32]
	mov edi, DWORD PTR [esi+56]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+16]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], ebp
	mov ebp, DWORD PTR [esi+40]
	xor ebp, DWORD PTR [esi+56]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 511060458
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+40]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+8]
	xor ebx, DWORD PTR [esi+36]
	mov edx, DWORD PTR [esi+60]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+20]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], ebx
	mov ebx, DWORD PTR [esi+44]
	xor ebx, DWORD PTR [esi+60]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 1022120916
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+44]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+24]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 2044241832
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+48]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+16]
	xor ebp, DWORD PTR [esi+44]
	mov edi, DWORD PTR [esi+4]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+28]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+56]
	mov DWORD PTR [esi+16], ebp
	mov ebp, DWORD PTR [esi+52]
	xor ebp, DWORD PTR [esi+4]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -206483632
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+52]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+20]
	xor ebx, DWORD PTR [esi+48]
	mov edx, DWORD PTR [esi+8]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+32]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+60]
	mov DWORD PTR [esi+20], ebx
	mov ebx, DWORD PTR [esi+56]
	xor ebx, DWORD PTR [esi+8]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -412967263
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+56]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+12]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+36]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+12]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -825934525
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+60]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+28]
	xor ebp, DWORD PTR [esi+56]
	mov edi, DWORD PTR [esi+16]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+40]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+4]
	mov DWORD PTR [esi+28], ebp
	mov ebp, DWORD PTR [esi]
	xor ebp, DWORD PTR [esi+16]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1651869049
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+32]
	xor ebx, DWORD PTR [esi+60]
	mov edx, DWORD PTR [esi+20]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+44]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+8]
	mov DWORD PTR [esi+32], ebx
	mov ebx, DWORD PTR [esi+4]
	xor ebx, DWORD PTR [esi+20]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 991229199
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+4]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+24]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+48]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+24]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 1982458398
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+8]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+40]
	xor ebp, DWORD PTR [esi+4]
	mov edi, DWORD PTR [esi+28]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+52]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+16]
	mov DWORD PTR [esi+40], ebp
	mov ebp, DWORD PTR [esi+12]
	xor ebp, DWORD PTR [esi+28]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -330050500
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+12]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+44]
	xor ebx, DWORD PTR [esi+8]
	mov edx, DWORD PTR [esi+32]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+56]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+20]
	mov DWORD PTR [esi+44], ebx
	mov ebx, DWORD PTR [esi+16]
	xor ebx, DWORD PTR [esi+32]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -660100999
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+16]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+36]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+60]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+36]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -1320201997
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+20]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+52]
	xor ebp, DWORD PTR [esi+16]
	mov edi, DWORD PTR [esi+40]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+28]
	mov DWORD PTR [esi+52], ebp
	mov ebp, DWORD PTR [esi+24]
	xor ebp, DWORD PTR [esi+40]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 1654563303
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+24]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+56]
	xor ebx, DWORD PTR [esi+20]
	mov edx, DWORD PTR [esi+44]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+4]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+32]
	mov DWORD PTR [esi+56], ebx
	mov ebx, DWORD PTR [esi+28]
	xor ebx, DWORD PTR [esi+44]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, -985840690
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+28]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+48]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+8]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+48]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -1971681379
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+32]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi]
	xor ebp, DWORD PTR [esi+28]
	mov edi, DWORD PTR [esi+52]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+12]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+40]
	mov DWORD PTR [esi], ebp
	mov ebp, DWORD PTR [esi+36]
	xor ebp, DWORD PTR [esi+52]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 351604539
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+36]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+4]
	xor ebx, DWORD PTR [esi+32]
	mov edx, DWORD PTR [esi+56]
	ror edx, 17
	xor ebx, edx
	mov edx, ebx
	ror edx, 17
	xor ebx, edx
	ror edx, 24
	xor ebx, edx
	mov edx, DWORD PTR [esi+16]
	ror edx, 25
	xor ebx, edx
	xor ebx, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], ebx
	mov ebx, DWORD PTR [esi+40]
	xor ebx, DWORD PTR [esi+56]
	add ebx, DWORD PTR [esi+64]
	mov edx, DWORD PTR [esi+68]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 703209078
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+40]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+60]
	ror ecx, 17
	xor eax, ecx
	mov ecx, eax
	ror ecx, 17
	xor eax, ecx
	ror ecx, 24
	xor eax, ecx
	mov ecx, DWORD PTR [esi+20]
	ror ecx, 25
	xor eax, ecx
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+60]
	add eax, DWORD PTR [esi+68]
	mov ecx, DWORD PTR [esi+64]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+68], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, 1406418156
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+44]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+12]
	xor ebp, DWORD PTR [esi+40]
	mov edi, DWORD PTR [esi]
	ror edi, 17
	xor ebp, edi
	mov edi, ebp
	ror edi, 17
	xor ebp, edi
	ror edi, 24
	xor ebp, edi
	mov edi, DWORD PTR [esi+24]
	ror edi, 25
	xor ebp, edi
	xor ebp, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], ebp
	mov ebp, DWORD PTR [esi+48]
	xor ebp, DWORD PTR [esi]
	add ebp, DWORD PTR [esi+64]
	mov edi, DWORD PTR [esi+68]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+64], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, -1482130984
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+48]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esi+52]
	xor ebx, DWORD PTR [esi+4]
	add ebx, DWORD PTR [esi+68]
	mov edx, DWORD PTR [esi+64]
	xor edx, eax
	xor eax, ebp
	and edx, eax
	xor eax, ebp
	xor edx, eax
	add ebx, edx
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, ebp
	ror eax, 20
	mov edx, eax
	add edx, 1330705329
	add edx, edi
	ror edx, 25
	xor eax, edx
	add ebx, eax
	mov eax, ecx
	xor eax, DWORD PTR [esi+80]
	ror ecx, 13
	mov DWORD PTR [esi+72], ecx
	mov ecx, DWORD PTR [esi+76]
	add ecx, DWORD PTR [esi+52]
	and eax, edi
	xor eax, DWORD PTR [esi+80]
	add edx, ecx
	add edx, eax
	mov eax, edx
	ror eax, 23
	xor edx, eax
	ror eax, 24
	xor edx, eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+8]
	add eax, DWORD PTR [esi+64]
	mov ecx, DWORD PTR [esi+68]
	xor ecx, ebp
	xor ebp, ebx
	and ecx, ebp
	xor ebp, ebx
	xor ecx, ebp
	add eax, ecx
	ror ebp, 23
	mov DWORD PTR [esi+64], ebp
	mov ebp, ebx
	ror ebp, 20
	mov ecx, ebp
	add ecx, -1633556638
	add ecx, edx
	ror ecx, 25
	xor ebp, ecx
	add eax, ebp
	mov ebp, edi
	xor ebp, DWORD PTR [esi+72]
	ror edi, 13
	mov DWORD PTR [esi+76], edi
	mov edi, DWORD PTR [esi+80]
	add edi, DWORD PTR [esi+56]
	and ebp, edx
	xor ebp, DWORD PTR [esi+72]
	add ecx, edi
	add ecx, ebp
	mov ebp, ecx
	ror ebp, 23
	xor ecx, ebp
	ror ebp, 24
	xor ecx, ebp
	mov ebp, DWORD PTR [esi+60]
	xor ebp, DWORD PTR [esi+12]
	add ebp, DWORD PTR [esi+68]
	mov edi, DWORD PTR [esi+64]
	xor edi, ebx
	xor ebx, eax
	and edi, ebx
	xor ebx, eax
	xor edi, ebx
	add ebp, edi
	ror ebx, 23
	mov DWORD PTR [esi+68], ebx
	mov ebx, eax
	ror ebx, 20
	mov edi, ebx
	add edi, 1027854021
	add edi, ecx
	ror edi, 25
	xor ebx, edi
	add ebp, ebx
	mov ebx, edx
	xor ebx, DWORD PTR [esi+76]
	ror edx, 13
	mov DWORD PTR [esi+80], edx
	mov edx, DWORD PTR [esi+72]
	add edx, DWORD PTR [esi+60]
	and ebx, ecx
	xor ebx, DWORD PTR [esi+76]
	add edi, edx
	add edi, ebx
	mov ebx, edi
	ror ebx, 23
	xor edi, ebx
	ror ebx, 24
	xor edi, ebx
	mov ebx, DWORD PTR [esp+4]
	xor ebp, DWORD PTR [ebx]
	mov DWORD PTR [ebx], ebp
	xor eax, DWORD PTR [ebx+4]
	mov DWORD PTR [ebx+4], eax
	mov edx, DWORD PTR [esi+68]
	xor edx, DWORD PTR [ebx+8]
	mov DWORD PTR [ebx+8], edx
	mov edx, DWORD PTR [esi+64]
	xor edx, DWORD PTR [ebx+12]
	mov DWORD PTR [ebx+12], edx
	xor edi, DWORD PTR [ebx+16]
	mov DWORD PTR [ebx+16], edi
	xor ecx, DWORD PTR [ebx+20]
	mov DWORD PTR [ebx+20], ecx
	mov edx, DWORD PTR [esi+80]
	xor edx, DWORD PTR [ebx+24]
	mov DWORD PTR [ebx+24], edx
	mov edx, DWORD PTR [esi+76]
	xor edx, DWORD PTR [ebx+28]
	mov DWORD PTR [ebx+28], edx
	mov edi, DWORD PTR [esi+84]
	mov ebp, DWORD PTR [esi+88]
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
