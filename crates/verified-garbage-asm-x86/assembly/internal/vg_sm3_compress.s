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
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, 2043430169
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+16]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+20]
	bswap eax
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -208106958
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+20]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+24]
	bswap eax
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, -416213915
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+24]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+28]
	bswap eax
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -832427829
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+28]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+32]
	bswap eax
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1664855657
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+32]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+36]
	bswap eax
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 965255983
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+36]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+40]
	bswap eax
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 1930511966
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+40]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+44]
	bswap eax
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -433943364
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+44]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+48]
	bswap eax
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -867886727
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+32]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+48]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+52]
	bswap eax
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -1735773453
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi+52]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+56]
	bswap eax
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 823420391
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+56]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+60]
	bswap eax
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1646840782
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+60]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1001285732
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -2002571463
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+4]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [esi+68]
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 289824371
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+8]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [esi+64]
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 579648742
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+12]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [esi+76]
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+28]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1651869049
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+16]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+8]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+32]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 991229199
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+20]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+36]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 1982458398
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+24]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+40]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -330050500
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+28]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+44]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -660100999
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+32]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+48]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -1320201997
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+36]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+28]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 1654563303
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+40]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+32]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -985840690
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+44]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+36]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1971681379
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+32]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+48]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+40]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 351604539
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi+52]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+44]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 703209078
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+56]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+48]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+8]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1406418156
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+60]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1482130984
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 1330705329
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+4]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, -1633556638
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+8]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1027854021
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+12]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+28]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, 2055708042
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+16]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+8]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+32]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -183551212
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+20]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+36]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, -367102423
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+24]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+40]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -734204845
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+28]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+44]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1468409689
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+32]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+48]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 1358147919
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+36]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+28]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, -1578671458
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+40]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+32]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1137624381
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+44]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+36]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -2019718534
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+32]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+48]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+40]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 255530229
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi+52]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+44]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 511060458
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+56]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+48]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+8]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1022120916
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+60]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, 2044241832
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -206483632
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+4]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, -412967263
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+8]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -825934525
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+12]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+44]
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+28]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+56]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1651869049
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+16]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+48]
	mov ebx, DWORD PTR [esi+8]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+32]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+60]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 991229199
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+20]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+52]
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+36]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 1982458398
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+24]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+56]
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+40]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+4]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -330050500
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+28]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+60]
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+44]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+8]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -660100999
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+16]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [esi+32]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi]
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+48]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+12]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, -1320201997
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+20]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [esi+36]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+4]
	mov ebx, DWORD PTR [esi+28]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+16]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 1654563303
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+24]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [esi+40]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+8]
	mov ebx, DWORD PTR [esi+32]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+20]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, -985840690
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+28]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [esi+44]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi+12]
	mov ebx, DWORD PTR [esi+36]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+24]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1971681379
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+32]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [esi+48]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+16]
	mov ebx, DWORD PTR [esi+40]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+28]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 351604539
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+36]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [esi+52]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+20]
	mov ebx, DWORD PTR [esi+44]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+4]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+32]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, 703209078
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+40]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [esi+56]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+24]
	mov ebx, DWORD PTR [esi+48]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+8]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+36]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1406418156
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+44]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [esi+60]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [esi+28]
	mov ebx, DWORD PTR [esi+52]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+12]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+40]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+64]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+80]
	add ebx, -1482130984
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+92]
	add edx, ebx
	add edx, DWORD PTR [esi+48]
	mov ecx, DWORD PTR [esi+76]
	add ecx, eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [esi]
	add ecx, eax
	mov eax, DWORD PTR [esi+64]
	or eax, DWORD PTR [esi+68]
	and eax, DWORD PTR [esi+72]
	mov ebx, DWORD PTR [esi+64]
	and ebx, DWORD PTR [esi+68]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+76], ecx
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+88]
	and eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+88]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+92], edx
	mov eax, DWORD PTR [esi+68]
	ror eax, 23
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+84]
	ror eax, 13
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [esi+32]
	mov ebx, DWORD PTR [esi+56]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+16]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+44]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+76]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+92]
	add ebx, 1330705329
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+88]
	add edx, ebx
	add edx, DWORD PTR [esi+52]
	mov ecx, DWORD PTR [esi+72]
	add ecx, eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [esi+4]
	add ecx, eax
	mov eax, DWORD PTR [esi+76]
	or eax, DWORD PTR [esi+64]
	and eax, DWORD PTR [esi+68]
	mov ebx, DWORD PTR [esi+76]
	and ebx, DWORD PTR [esi+64]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+72], ecx
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [esi+84]
	and eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+84]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+88], edx
	mov eax, DWORD PTR [esi+64]
	ror eax, 23
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+80]
	ror eax, 13
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [esi+36]
	mov ebx, DWORD PTR [esi+60]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+20]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+48]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+72]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+88]
	add ebx, -1633556638
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+84]
	add edx, ebx
	add edx, DWORD PTR [esi+56]
	mov ecx, DWORD PTR [esi+68]
	add ecx, eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [esi+8]
	add ecx, eax
	mov eax, DWORD PTR [esi+72]
	or eax, DWORD PTR [esi+76]
	and eax, DWORD PTR [esi+64]
	mov ebx, DWORD PTR [esi+72]
	and ebx, DWORD PTR [esi+76]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+68], ecx
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [esi+80]
	and eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+80]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+84], edx
	mov eax, DWORD PTR [esi+76]
	ror eax, 23
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+92]
	ror eax, 13
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [esi+40]
	mov ebx, DWORD PTR [esi]
	ror ebx, 17
	xor eax, ebx
	mov ebx, eax
	ror ebx, 17
	mov ecx, eax
	ror ecx, 9
	xor eax, ebx
	xor eax, ecx
	mov ebx, DWORD PTR [esi+24]
	ror ebx, 25
	xor eax, ebx
	xor eax, DWORD PTR [esi+52]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+68]
	ror eax, 20
	mov ebx, eax
	add ebx, DWORD PTR [esi+84]
	add ebx, 1027854021
	ror ebx, 25
	xor eax, ebx
	mov edx, DWORD PTR [esi+80]
	add edx, ebx
	add edx, DWORD PTR [esi+60]
	mov ecx, DWORD PTR [esi+64]
	add ecx, eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [esi+12]
	add ecx, eax
	mov eax, DWORD PTR [esi+68]
	or eax, DWORD PTR [esi+72]
	and eax, DWORD PTR [esi+76]
	mov ebx, DWORD PTR [esi+68]
	and ebx, DWORD PTR [esi+72]
	or eax, ebx
	add ecx, eax
	mov DWORD PTR [esi+64], ecx
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [esi+92]
	and eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [esi+92]
	add edx, eax
	mov eax, edx
	ror eax, 23
	mov ebx, edx
	ror ebx, 15
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [esi+80], edx
	mov eax, DWORD PTR [esi+72]
	ror eax, 23
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+88]
	ror eax, 13
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esp+4]
	mov ebx, DWORD PTR [esi+64]
	xor ebx, DWORD PTR [eax]
	mov DWORD PTR [eax], ebx
	mov ebx, DWORD PTR [esi+68]
	xor ebx, DWORD PTR [eax+4]
	mov DWORD PTR [eax+4], ebx
	mov ebx, DWORD PTR [esi+72]
	xor ebx, DWORD PTR [eax+8]
	mov DWORD PTR [eax+8], ebx
	mov ebx, DWORD PTR [esi+76]
	xor ebx, DWORD PTR [eax+12]
	mov DWORD PTR [eax+12], ebx
	mov ebx, DWORD PTR [esi+80]
	xor ebx, DWORD PTR [eax+16]
	mov DWORD PTR [eax+16], ebx
	mov ebx, DWORD PTR [esi+84]
	xor ebx, DWORD PTR [eax+20]
	mov DWORD PTR [eax+20], ebx
	mov ebx, DWORD PTR [esi+88]
	xor ebx, DWORD PTR [eax+24]
	mov DWORD PTR [eax+24], ebx
	mov ebx, DWORD PTR [esi+92]
	xor ebx, DWORD PTR [eax+28]
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
