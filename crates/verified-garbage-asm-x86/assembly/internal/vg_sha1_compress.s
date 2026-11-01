// The functions of `src/internal/vg_sha1_compress.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+64], ebx
	mov DWORD PTR [eax+68], esi
	mov DWORD PTR [eax+72], edi
	mov DWORD PTR [eax+76], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+80], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+84], ecx
	test ecx, ecx
	je 20f
22:
	mov edi, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+8]
	mov edx, DWORD PTR [edi+12]
	mov esi, DWORD PTR [edi+16]
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi]
	bswap edi
	mov DWORD PTR [ebp], edi
	add esi, edi
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1518500249
	ror ebx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+4]
	bswap edi
	mov DWORD PTR [ebp+4], edi
	add edx, edi
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1518500249
	ror eax, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+8]
	bswap edi
	mov DWORD PTR [ebp+8], edi
	add ecx, edi
	mov edi, eax
	xor edi, ebx
	and edi, esi
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1518500249
	ror esi, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+12]
	bswap edi
	mov DWORD PTR [ebp+12], edi
	add ebx, edi
	mov edi, esi
	xor edi, eax
	and edi, edx
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1518500249
	ror edx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+16]
	bswap edi
	mov DWORD PTR [ebp+16], edi
	add eax, edi
	mov edi, edx
	xor edi, esi
	and edi, ecx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1518500249
	ror ecx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+20]
	bswap edi
	mov DWORD PTR [ebp+20], edi
	add esi, edi
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1518500249
	ror ebx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+24]
	bswap edi
	mov DWORD PTR [ebp+24], edi
	add edx, edi
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1518500249
	ror eax, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+28]
	bswap edi
	mov DWORD PTR [ebp+28], edi
	add ecx, edi
	mov edi, eax
	xor edi, ebx
	and edi, esi
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1518500249
	ror esi, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+32]
	bswap edi
	mov DWORD PTR [ebp+32], edi
	add ebx, edi
	mov edi, esi
	xor edi, eax
	and edi, edx
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1518500249
	ror edx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+36]
	bswap edi
	mov DWORD PTR [ebp+36], edi
	add eax, edi
	mov edi, edx
	xor edi, esi
	and edi, ecx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1518500249
	ror ecx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+40]
	bswap edi
	mov DWORD PTR [ebp+40], edi
	add esi, edi
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1518500249
	ror ebx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+44]
	bswap edi
	mov DWORD PTR [ebp+44], edi
	add edx, edi
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1518500249
	ror eax, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+48]
	bswap edi
	mov DWORD PTR [ebp+48], edi
	add ecx, edi
	mov edi, eax
	xor edi, ebx
	and edi, esi
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1518500249
	ror esi, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+52]
	bswap edi
	mov DWORD PTR [ebp+52], edi
	add ebx, edi
	mov edi, esi
	xor edi, eax
	and edi, edx
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1518500249
	ror edx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+56]
	bswap edi
	mov DWORD PTR [ebp+56], edi
	add eax, edi
	mov edi, edx
	xor edi, esi
	and edi, ecx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1518500249
	ror ecx, 2
	mov edi, DWORD PTR [ebp+80]
	mov edi, DWORD PTR [edi+60]
	bswap edi
	mov DWORD PTR [ebp+60], edi
	add esi, edi
	mov edi, ecx
	xor edi, edx
	and edi, ebx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1518500249
	ror ebx, 2
	mov edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp]
	ror edi, 31
	mov DWORD PTR [ebp], edi
	add edx, edi
	mov edi, ebx
	xor edi, ecx
	and edi, eax
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1518500249
	ror eax, 2
	mov edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+4]
	ror edi, 31
	mov DWORD PTR [ebp+4], edi
	add ecx, edi
	mov edi, eax
	xor edi, ebx
	and edi, esi
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1518500249
	ror esi, 2
	mov edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+8]
	ror edi, 31
	mov DWORD PTR [ebp+8], edi
	add ebx, edi
	mov edi, esi
	xor edi, eax
	and edi, edx
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1518500249
	ror edx, 2
	mov edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	ror edi, 31
	mov DWORD PTR [ebp+12], edi
	add eax, edi
	mov edi, edx
	xor edi, esi
	and edi, ecx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1518500249
	ror ecx, 2
	mov edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+16]
	ror edi, 31
	mov DWORD PTR [ebp+16], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1859775393
	ror ebx, 2
	mov edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+20]
	ror edi, 31
	mov DWORD PTR [ebp+20], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1859775393
	ror eax, 2
	mov edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+24]
	ror edi, 31
	mov DWORD PTR [ebp+24], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1859775393
	ror esi, 2
	mov edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+28]
	ror edi, 31
	mov DWORD PTR [ebp+28], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1859775393
	ror edx, 2
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+32]
	ror edi, 31
	mov DWORD PTR [ebp+32], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1859775393
	ror ecx, 2
	mov edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+36]
	ror edi, 31
	mov DWORD PTR [ebp+36], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1859775393
	ror ebx, 2
	mov edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+40]
	ror edi, 31
	mov DWORD PTR [ebp+40], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1859775393
	ror eax, 2
	mov edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+44]
	ror edi, 31
	mov DWORD PTR [ebp+44], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1859775393
	ror esi, 2
	mov edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+48]
	ror edi, 31
	mov DWORD PTR [ebp+48], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1859775393
	ror edx, 2
	mov edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+52]
	ror edi, 31
	mov DWORD PTR [ebp+52], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1859775393
	ror ecx, 2
	mov edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+56]
	ror edi, 31
	mov DWORD PTR [ebp+56], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1859775393
	ror ebx, 2
	mov edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+60]
	ror edi, 31
	mov DWORD PTR [ebp+60], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1859775393
	ror eax, 2
	mov edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp]
	ror edi, 31
	mov DWORD PTR [ebp], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1859775393
	ror esi, 2
	mov edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+4]
	ror edi, 31
	mov DWORD PTR [ebp+4], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1859775393
	ror edx, 2
	mov edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+8]
	ror edi, 31
	mov DWORD PTR [ebp+8], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1859775393
	ror ecx, 2
	mov edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	ror edi, 31
	mov DWORD PTR [ebp+12], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, 1859775393
	ror ebx, 2
	mov edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+16]
	ror edi, 31
	mov DWORD PTR [ebp+16], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, 1859775393
	ror eax, 2
	mov edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+20]
	ror edi, 31
	mov DWORD PTR [ebp+20], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, 1859775393
	ror esi, 2
	mov edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+24]
	ror edi, 31
	mov DWORD PTR [ebp+24], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, 1859775393
	ror edx, 2
	mov edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+28]
	ror edi, 31
	mov DWORD PTR [ebp+28], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, 1859775393
	ror ecx, 2
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+32]
	ror edi, 31
	mov DWORD PTR [ebp+32], edi
	add esi, edi
	mov edi, ebx
	and edi, ecx
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -1894007588
	ror ebx, 2
	mov edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+36]
	ror edi, 31
	mov DWORD PTR [ebp+36], edi
	add edx, edi
	mov edi, eax
	and edi, ebx
	add edx, edi
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -1894007588
	ror eax, 2
	mov edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+40]
	ror edi, 31
	mov DWORD PTR [ebp+40], edi
	add ecx, edi
	mov edi, esi
	and edi, eax
	add ecx, edi
	mov edi, esi
	xor edi, eax
	and edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -1894007588
	ror esi, 2
	mov edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+44]
	ror edi, 31
	mov DWORD PTR [ebp+44], edi
	add ebx, edi
	mov edi, edx
	and edi, esi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	and edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -1894007588
	ror edx, 2
	mov edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+48]
	ror edi, 31
	mov DWORD PTR [ebp+48], edi
	add eax, edi
	mov edi, ecx
	and edi, edx
	add eax, edi
	mov edi, ecx
	xor edi, edx
	and edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -1894007588
	ror ecx, 2
	mov edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+52]
	ror edi, 31
	mov DWORD PTR [ebp+52], edi
	add esi, edi
	mov edi, ebx
	and edi, ecx
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -1894007588
	ror ebx, 2
	mov edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+56]
	ror edi, 31
	mov DWORD PTR [ebp+56], edi
	add edx, edi
	mov edi, eax
	and edi, ebx
	add edx, edi
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -1894007588
	ror eax, 2
	mov edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+60]
	ror edi, 31
	mov DWORD PTR [ebp+60], edi
	add ecx, edi
	mov edi, esi
	and edi, eax
	add ecx, edi
	mov edi, esi
	xor edi, eax
	and edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -1894007588
	ror esi, 2
	mov edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp]
	ror edi, 31
	mov DWORD PTR [ebp], edi
	add ebx, edi
	mov edi, edx
	and edi, esi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	and edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -1894007588
	ror edx, 2
	mov edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+4]
	ror edi, 31
	mov DWORD PTR [ebp+4], edi
	add eax, edi
	mov edi, ecx
	and edi, edx
	add eax, edi
	mov edi, ecx
	xor edi, edx
	and edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -1894007588
	ror ecx, 2
	mov edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+8]
	ror edi, 31
	mov DWORD PTR [ebp+8], edi
	add esi, edi
	mov edi, ebx
	and edi, ecx
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -1894007588
	ror ebx, 2
	mov edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	ror edi, 31
	mov DWORD PTR [ebp+12], edi
	add edx, edi
	mov edi, eax
	and edi, ebx
	add edx, edi
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -1894007588
	ror eax, 2
	mov edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+16]
	ror edi, 31
	mov DWORD PTR [ebp+16], edi
	add ecx, edi
	mov edi, esi
	and edi, eax
	add ecx, edi
	mov edi, esi
	xor edi, eax
	and edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -1894007588
	ror esi, 2
	mov edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+20]
	ror edi, 31
	mov DWORD PTR [ebp+20], edi
	add ebx, edi
	mov edi, edx
	and edi, esi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	and edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -1894007588
	ror edx, 2
	mov edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+24]
	ror edi, 31
	mov DWORD PTR [ebp+24], edi
	add eax, edi
	mov edi, ecx
	and edi, edx
	add eax, edi
	mov edi, ecx
	xor edi, edx
	and edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -1894007588
	ror ecx, 2
	mov edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+28]
	ror edi, 31
	mov DWORD PTR [ebp+28], edi
	add esi, edi
	mov edi, ebx
	and edi, ecx
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	and edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -1894007588
	ror ebx, 2
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+32]
	ror edi, 31
	mov DWORD PTR [ebp+32], edi
	add edx, edi
	mov edi, eax
	and edi, ebx
	add edx, edi
	mov edi, eax
	xor edi, ebx
	and edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -1894007588
	ror eax, 2
	mov edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+36]
	ror edi, 31
	mov DWORD PTR [ebp+36], edi
	add ecx, edi
	mov edi, esi
	and edi, eax
	add ecx, edi
	mov edi, esi
	xor edi, eax
	and edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -1894007588
	ror esi, 2
	mov edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+40]
	ror edi, 31
	mov DWORD PTR [ebp+40], edi
	add ebx, edi
	mov edi, edx
	and edi, esi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	and edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -1894007588
	ror edx, 2
	mov edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+44]
	ror edi, 31
	mov DWORD PTR [ebp+44], edi
	add eax, edi
	mov edi, ecx
	and edi, edx
	add eax, edi
	mov edi, ecx
	xor edi, edx
	and edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -1894007588
	ror ecx, 2
	mov edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+48]
	ror edi, 31
	mov DWORD PTR [ebp+48], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -899497514
	ror ebx, 2
	mov edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+52]
	ror edi, 31
	mov DWORD PTR [ebp+52], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -899497514
	ror eax, 2
	mov edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+56]
	ror edi, 31
	mov DWORD PTR [ebp+56], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -899497514
	ror esi, 2
	mov edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+60]
	ror edi, 31
	mov DWORD PTR [ebp+60], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -899497514
	ror edx, 2
	mov edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp]
	ror edi, 31
	mov DWORD PTR [ebp], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -899497514
	ror ecx, 2
	mov edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+4]
	ror edi, 31
	mov DWORD PTR [ebp+4], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -899497514
	ror ebx, 2
	mov edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+8]
	ror edi, 31
	mov DWORD PTR [ebp+8], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -899497514
	ror eax, 2
	mov edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+12]
	ror edi, 31
	mov DWORD PTR [ebp+12], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -899497514
	ror esi, 2
	mov edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+16]
	ror edi, 31
	mov DWORD PTR [ebp+16], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -899497514
	ror edx, 2
	mov edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+20]
	ror edi, 31
	mov DWORD PTR [ebp+20], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -899497514
	ror ecx, 2
	mov edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+24]
	ror edi, 31
	mov DWORD PTR [ebp+24], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -899497514
	ror ebx, 2
	mov edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+28]
	ror edi, 31
	mov DWORD PTR [ebp+28], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -899497514
	ror eax, 2
	mov edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+32]
	ror edi, 31
	mov DWORD PTR [ebp+32], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -899497514
	ror esi, 2
	mov edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+36]
	ror edi, 31
	mov DWORD PTR [ebp+36], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -899497514
	ror edx, 2
	mov edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+8]
	xor edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+40]
	ror edi, 31
	mov DWORD PTR [ebp+40], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -899497514
	ror ecx, 2
	mov edi, DWORD PTR [ebp+32]
	xor edi, DWORD PTR [ebp+12]
	xor edi, DWORD PTR [ebp+52]
	xor edi, DWORD PTR [ebp+44]
	ror edi, 31
	mov DWORD PTR [ebp+44], edi
	add esi, edi
	mov edi, ebx
	xor edi, ecx
	xor edi, edx
	add esi, edi
	mov edi, eax
	ror edi, 27
	add esi, edi
	add esi, -899497514
	ror ebx, 2
	mov edi, DWORD PTR [ebp+36]
	xor edi, DWORD PTR [ebp+16]
	xor edi, DWORD PTR [ebp+56]
	xor edi, DWORD PTR [ebp+48]
	ror edi, 31
	mov DWORD PTR [ebp+48], edi
	add edx, edi
	mov edi, eax
	xor edi, ebx
	xor edi, ecx
	add edx, edi
	mov edi, esi
	ror edi, 27
	add edx, edi
	add edx, -899497514
	ror eax, 2
	mov edi, DWORD PTR [ebp+40]
	xor edi, DWORD PTR [ebp+20]
	xor edi, DWORD PTR [ebp+60]
	xor edi, DWORD PTR [ebp+52]
	ror edi, 31
	mov DWORD PTR [ebp+52], edi
	add ecx, edi
	mov edi, esi
	xor edi, eax
	xor edi, ebx
	add ecx, edi
	mov edi, edx
	ror edi, 27
	add ecx, edi
	add ecx, -899497514
	ror esi, 2
	mov edi, DWORD PTR [ebp+44]
	xor edi, DWORD PTR [ebp+24]
	xor edi, DWORD PTR [ebp]
	xor edi, DWORD PTR [ebp+56]
	ror edi, 31
	mov DWORD PTR [ebp+56], edi
	add ebx, edi
	mov edi, edx
	xor edi, esi
	xor edi, eax
	add ebx, edi
	mov edi, ecx
	ror edi, 27
	add ebx, edi
	add ebx, -899497514
	ror edx, 2
	mov edi, DWORD PTR [ebp+48]
	xor edi, DWORD PTR [ebp+28]
	xor edi, DWORD PTR [ebp+4]
	xor edi, DWORD PTR [ebp+60]
	ror edi, 31
	mov DWORD PTR [ebp+60], edi
	add eax, edi
	mov edi, ecx
	xor edi, edx
	xor edi, esi
	add eax, edi
	mov edi, ebx
	ror edi, 27
	add eax, edi
	add eax, -899497514
	ror ecx, 2
	mov edi, DWORD PTR [esp+4]
	add eax, DWORD PTR [edi]
	add ebx, DWORD PTR [edi+4]
	add ecx, DWORD PTR [edi+8]
	add edx, DWORD PTR [edi+12]
	add esi, DWORD PTR [edi+16]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov DWORD PTR [edi+8], ecx
	mov DWORD PTR [edi+12], edx
	mov DWORD PTR [edi+16], esi
	mov eax, DWORD PTR [ebp+80]
	add eax, 64
	mov DWORD PTR [ebp+80], eax
	mov eax, DWORD PTR [ebp+84]
	sub eax, 1
	mov DWORD PTR [ebp+84], eax
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [ebp+64]
	mov esi, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [ebp+72]
	mov ebp, DWORD PTR [ebp+76]
	ret
	.p2align 6
