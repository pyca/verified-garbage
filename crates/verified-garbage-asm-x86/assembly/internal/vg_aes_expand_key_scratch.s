// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+256], ebx
	mov DWORD PTR [eax+260], esi
	mov DWORD PTR [eax+264], edi
	mov DWORD PTR [eax+268], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+8]
20:
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [ebp], eax
	add esi, 4
	add ebp, 4
	sub ecx, 4
	jne 20b
	mov esi, ebp
	sub esi, 4
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [edi+280], eax
	shr eax, 2
	mov ebx, eax
	add eax, eax
	add eax, ebx
	add eax, 28
	mov DWORD PTR [edi+284], eax
	mov eax, 1
	mov DWORD PTR [edi+272], eax
21:
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [edi+276]
	test ecx, ecx
	je 22f
	cmp ecx, 16
	je 24f
	jmp 25f
24:
	mov ecx, DWORD PTR [edi+280]
	cmp ecx, 32
	je 26f
	jmp 27f
26:
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+8]
	mov ebp, DWORD PTR [edi+24]
	xor ebp, DWORD PTR [edi+20]
	mov DWORD PTR [edi+32], ecx
	mov ecx, ebp
	xor ecx, DWORD PTR [edi]
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, ebx
	xor ebp, eax
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+48], eax
	mov eax, ecx
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], ecx
	mov ecx, eax
	xor ecx, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+12]
	xor eax, ebp
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	xor ecx, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+64], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi]
	mov DWORD PTR [edi+68], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+72], ecx
	mov ecx, eax
	xor ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi]
	xor eax, ecx
	mov DWORD PTR [edi+80], eax
	mov eax, ebp
	xor eax, ecx
	mov DWORD PTR [edi+84], eax
	mov eax, ebp
	xor eax, edx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	mov DWORD PTR [edi+36], ebp
	mov ebp, ebx
	xor ebp, eax
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, eax
	mov DWORD PTR [edi+96], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+72]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+60]
	and edx, DWORD PTR [edi+68]
	xor edx, ebp
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi]
	xor edx, ebp
	mov ebp, ebx
	and ebp, eax
	mov DWORD PTR [edi+108], ebx
	mov ebx, DWORD PTR [edi+56]
	and ebx, DWORD PTR [edi+52]
	xor ebx, ebp
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+48]
	and eax, DWORD PTR [edi+80]
	xor eax, ebp
	mov ebp, DWORD PTR [edi+32]
	and ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+84]
	xor ecx, ebp
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+36]
	xor eax, ebp
	mov ebp, DWORD PTR [edi+104]
	xor ebp, ecx
	xor edx, eax
	xor ebx, ecx
	xor eax, DWORD PTR [edi+120]
	xor ebp, DWORD PTR [edi+76]
	xor edx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, edx
	and ebp, ebx
	mov DWORD PTR [edi+96], ebx
	mov ebx, eax
	xor ebx, ebp
	mov DWORD PTR [edi+92], ebp
	mov ebp, ecx
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+88], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	xor edx, DWORD PTR [edi+92]
	and edx, ecx
	xor edx, eax
	mov ecx, DWORD PTR [edi+96]
	xor ecx, edx
	mov DWORD PTR [edi+96], ebp
	mov ebp, ebx
	xor ebp, edx
	and eax, ebp
	xor ecx, eax
	xor ebx, eax
	and ebx, DWORD PTR [edi+96]
	xor ebx, DWORD PTR [edi+88]
	mov eax, ebx
	xor eax, ecx
	mov ebp, DWORD PTR [edi+96]
	xor ebp, edx
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+96]
	xor ebp, ebx
	mov DWORD PTR [edi+92], ebx
	mov ebx, edx
	xor ebx, ecx
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+88]
	xor ebp, eax
	mov DWORD PTR [edi+120], eax
	mov eax, ebx
	and eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], eax
	mov eax, ecx
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], eax
	mov eax, edx
	and eax, DWORD PTR [edi]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+92]
	and eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+96]
	and eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+36]
	and ebx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+60]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+92]
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+96]
	and ebx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebx
	mov ebx, DWORD PTR [edi+88]
	and ebx, DWORD PTR [edi+32]
	and ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+100]
	xor ebx, ebp
	xor edx, ecx
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+80]
	xor edx, DWORD PTR [edi+44]
	xor ecx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], ebx
	mov ebx, DWORD PTR [edi+72]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+72], ebx
	mov ebx, DWORD PTR [edi+116]
	xor ebx, DWORD PTR [edi+84]
	xor ebp, eax
	mov eax, DWORD PTR [edi+108]
	xor eax, edx
	xor ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+108], ebp
	mov ebp, DWORD PTR [edi+52]
	xor ebp, DWORD PTR [edi+44]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, ecx
	xor ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+40]
	xor edx, ebp
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+52]
	xor eax, ebx
	xor ecx, edx
	mov DWORD PTR [edi+52], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, ebp
	xor ebx, ebp
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov ebp, DWORD PTR [edi+112]
	xor ebp, DWORD PTR [edi+48]
	xor ebp, -1
	mov DWORD PTR [edi+48], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+112], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, ecx
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+100]
	xor ecx, DWORD PTR [edi+52]
	xor eax, edx
	xor eax, -1
	xor ebp, DWORD PTR [edi+108]
	xor ebp, -1
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+20], ebp
	mov DWORD PTR [edi+16], edx
	mov DWORD PTR [edi+8], ecx
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
27:
25:
	jmp 23f
22:
	mov DWORD PTR [edi], eax
	mov eax, 0
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi+16]
	xor eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+28]
	xor ebx, DWORD PTR [edi+4]
	mov ecx, DWORD PTR [edi+28]
	xor ecx, DWORD PTR [edi+16]
	mov edx, DWORD PTR [edi+28]
	xor edx, DWORD PTR [edi+8]
	mov ebp, DWORD PTR [edi+24]
	xor ebp, DWORD PTR [edi+20]
	mov DWORD PTR [edi+32], ecx
	mov ecx, ebp
	xor ecx, DWORD PTR [edi]
	mov DWORD PTR [edi+36], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi+16]
	mov DWORD PTR [edi+40], ebp
	mov ebp, ebx
	xor ebp, eax
	mov DWORD PTR [edi+44], eax
	mov eax, ecx
	xor eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+48], eax
	mov eax, ecx
	xor eax, DWORD PTR [edi+4]
	mov DWORD PTR [edi+52], ecx
	mov ecx, eax
	xor ecx, edx
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+12]
	xor eax, ebp
	mov DWORD PTR [edi+60], ecx
	mov ecx, eax
	xor ecx, DWORD PTR [edi+8]
	xor eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+64], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi]
	mov DWORD PTR [edi+68], ebp
	mov ebp, ecx
	xor ebp, DWORD PTR [edi+36]
	mov DWORD PTR [edi+72], ecx
	mov ecx, eax
	xor ecx, DWORD PTR [edi+32]
	mov DWORD PTR [edi+76], eax
	mov eax, DWORD PTR [edi]
	xor eax, ecx
	mov DWORD PTR [edi+80], eax
	mov eax, ebp
	xor eax, ecx
	mov DWORD PTR [edi+84], eax
	mov eax, ebp
	xor eax, edx
	mov DWORD PTR [edi+88], eax
	mov eax, DWORD PTR [edi+36]
	xor eax, ecx
	mov DWORD PTR [edi+36], ebp
	mov ebp, ebx
	xor ebp, eax
	mov DWORD PTR [edi+92], ebp
	mov ebp, DWORD PTR [edi+28]
	xor ebp, eax
	mov DWORD PTR [edi+96], ebp
	mov ebp, DWORD PTR [edi+64]
	and ebp, DWORD PTR [edi+72]
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+60]
	and edx, DWORD PTR [edi+68]
	xor edx, ebp
	mov DWORD PTR [edi+104], edx
	mov edx, DWORD PTR [edi+40]
	and edx, DWORD PTR [edi]
	xor edx, ebp
	mov ebp, ebx
	and ebp, eax
	mov DWORD PTR [edi+108], ebx
	mov ebx, DWORD PTR [edi+56]
	and ebx, DWORD PTR [edi+52]
	xor ebx, ebp
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+48]
	and eax, DWORD PTR [edi+80]
	xor eax, ebp
	mov ebp, DWORD PTR [edi+32]
	and ebp, ecx
	mov DWORD PTR [edi+116], ecx
	mov ecx, DWORD PTR [edi+44]
	and ecx, DWORD PTR [edi+84]
	xor ecx, ebp
	mov DWORD PTR [edi+120], eax
	mov eax, DWORD PTR [edi+100]
	and eax, DWORD PTR [edi+36]
	xor eax, ebp
	mov ebp, DWORD PTR [edi+104]
	xor ebp, ecx
	xor edx, eax
	xor ebx, ecx
	xor eax, DWORD PTR [edi+120]
	xor ebp, DWORD PTR [edi+76]
	xor edx, DWORD PTR [edi+88]
	xor ebx, DWORD PTR [edi+92]
	xor eax, DWORD PTR [edi+96]
	mov ecx, ebp
	xor ecx, edx
	and ebp, ebx
	mov DWORD PTR [edi+96], ebx
	mov ebx, eax
	xor ebx, ebp
	mov DWORD PTR [edi+92], ebp
	mov ebp, ecx
	and ebp, ebx
	xor ebp, edx
	mov DWORD PTR [edi+88], ecx
	mov ecx, DWORD PTR [edi+96]
	xor ecx, eax
	xor edx, DWORD PTR [edi+92]
	and edx, ecx
	xor edx, eax
	mov ecx, DWORD PTR [edi+96]
	xor ecx, edx
	mov DWORD PTR [edi+96], ebp
	mov ebp, ebx
	xor ebp, edx
	and eax, ebp
	xor ecx, eax
	xor ebx, eax
	and ebx, DWORD PTR [edi+96]
	xor ebx, DWORD PTR [edi+88]
	mov eax, ebx
	xor eax, ecx
	mov ebp, DWORD PTR [edi+96]
	xor ebp, edx
	mov DWORD PTR [edi+88], ebp
	mov ebp, DWORD PTR [edi+96]
	xor ebp, ebx
	mov DWORD PTR [edi+92], ebx
	mov ebx, edx
	xor ebx, ecx
	mov DWORD PTR [edi+76], ebp
	mov ebp, DWORD PTR [edi+88]
	xor ebp, eax
	mov DWORD PTR [edi+120], eax
	mov eax, ebx
	and eax, DWORD PTR [edi+72]
	mov DWORD PTR [edi+72], eax
	mov eax, ecx
	and eax, DWORD PTR [edi+68]
	mov DWORD PTR [edi+68], eax
	mov eax, edx
	and eax, DWORD PTR [edi]
	mov DWORD PTR [edi+104], eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], eax
	mov eax, DWORD PTR [edi+92]
	and eax, DWORD PTR [edi+52]
	mov DWORD PTR [edi+52], eax
	mov eax, DWORD PTR [edi+96]
	and eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], eax
	mov eax, DWORD PTR [edi+88]
	and eax, DWORD PTR [edi+116]
	mov DWORD PTR [edi+116], eax
	mov eax, ebp
	and eax, DWORD PTR [edi+84]
	mov DWORD PTR [edi+84], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+36]
	and ebx, DWORD PTR [edi+64]
	and ecx, DWORD PTR [edi+60]
	and edx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], eax
	mov eax, DWORD PTR [edi+76]
	and eax, DWORD PTR [edi+108]
	mov DWORD PTR [edi+108], eax
	mov eax, DWORD PTR [edi+92]
	and eax, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ebx
	mov ebx, DWORD PTR [edi+96]
	and ebx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], ebx
	mov ebx, DWORD PTR [edi+88]
	and ebx, DWORD PTR [edi+32]
	and ebp, DWORD PTR [edi+44]
	mov DWORD PTR [edi+44], eax
	mov eax, DWORD PTR [edi+120]
	and eax, DWORD PTR [edi+100]
	xor ebx, ebp
	xor edx, ecx
	mov DWORD PTR [edi+100], edx
	mov edx, DWORD PTR [edi+80]
	xor edx, DWORD PTR [edi+44]
	xor ecx, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], ecx
	mov ecx, DWORD PTR [edi+104]
	xor ecx, DWORD PTR [edi+108]
	mov DWORD PTR [edi+44], ebx
	mov ebx, DWORD PTR [edi+104]
	xor ebx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ebx
	mov ebx, DWORD PTR [edi+84]
	xor ebx, DWORD PTR [edi+40]
	mov DWORD PTR [edi+40], ebx
	mov ebx, DWORD PTR [edi+72]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+72], ebx
	mov ebx, DWORD PTR [edi+116]
	xor ebx, DWORD PTR [edi+84]
	xor ebp, eax
	mov eax, DWORD PTR [edi+108]
	xor eax, edx
	xor ecx, DWORD PTR [edi+72]
	mov DWORD PTR [edi+108], ebp
	mov ebp, DWORD PTR [edi+52]
	xor ebp, DWORD PTR [edi+44]
	xor ebx, DWORD PTR [edi+112]
	mov DWORD PTR [edi+112], edx
	mov edx, DWORD PTR [edi+44]
	xor edx, ecx
	xor ecx, DWORD PTR [edi+48]
	mov DWORD PTR [edi+48], edx
	mov edx, DWORD PTR [edi+40]
	xor edx, ebp
	xor ebp, DWORD PTR [edi+56]
	mov DWORD PTR [edi+56], eax
	mov eax, DWORD PTR [edi+52]
	xor eax, ebx
	xor ecx, edx
	mov DWORD PTR [edi+52], ecx
	mov ecx, DWORD PTR [edi+68]
	xor ecx, ebp
	xor ebx, ebp
	xor edx, DWORD PTR [edi+56]
	xor edx, -1
	mov ebp, DWORD PTR [edi+112]
	xor ebp, DWORD PTR [edi+48]
	xor ebp, -1
	mov DWORD PTR [edi+48], ebp
	mov ebp, eax
	xor ebp, DWORD PTR [edi+52]
	mov DWORD PTR [edi+112], edx
	mov edx, DWORD PTR [edi+72]
	xor edx, ecx
	xor ecx, DWORD PTR [edi+80]
	mov DWORD PTR [edi+80], ecx
	mov ecx, DWORD PTR [edi+100]
	xor ecx, DWORD PTR [edi+52]
	xor eax, edx
	xor eax, -1
	xor ebp, DWORD PTR [edi+108]
	xor ebp, -1
	mov DWORD PTR [edi+28], ebx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+20], ebp
	mov DWORD PTR [edi+16], edx
	mov DWORD PTR [edi+8], ecx
	mov eax, DWORD PTR [edi+80]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+112]
	mov DWORD PTR [edi+4], eax
	mov eax, DWORD PTR [edi+48]
	mov DWORD PTR [edi], eax
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+4]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+24]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 1
	xor ecx, ebx
	and ecx, 1431655765
	xor ebx, ecx
	ror ecx, 31
	xor eax, ecx
	mov DWORD PTR [edi+24], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+8]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+8], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+12]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+12], ebx
	mov eax, DWORD PTR [edi+16]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+16], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+20]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 2
	xor ecx, ebx
	and ecx, 858993459
	xor ebx, ecx
	ror ecx, 30
	xor eax, ecx
	mov DWORD PTR [edi+20], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	mov ebx, DWORD PTR [edi+16]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+16], ebx
	mov eax, DWORD PTR [edi+4]
	mov ebx, DWORD PTR [edi+20]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+4], eax
	mov DWORD PTR [edi+20], ebx
	mov eax, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+24]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+8], eax
	mov DWORD PTR [edi+24], ebx
	mov eax, DWORD PTR [edi+12]
	mov ebx, DWORD PTR [edi+28]
	mov ecx, eax
	shr ecx, 4
	xor ecx, ebx
	and ecx, 252645135
	xor ebx, ecx
	ror ecx, 28
	xor eax, ecx
	mov DWORD PTR [edi+12], eax
	mov DWORD PTR [edi+28], ebx
	mov eax, DWORD PTR [edi]
	ror eax, 8
	xor eax, DWORD PTR [edi+272]
	mov ebx, DWORD PTR [edi+272]
	mov ecx, ebx
	shr ecx, 7
	mov edx, 0
	sub edx, ecx
	and edx, 27
	add ebx, ebx
	xor ebx, edx
	and ebx, 255
	mov DWORD PTR [edi+272], ebx
23:
	mov ecx, DWORD PTR [edi+280]
	mov ebx, esi
	add ebx, 4
	sub ebx, ecx
	xor eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [edi+276]
	mov edx, DWORD PTR [edi+284]
	mov ebp, DWORD PTR [edi+280]
	mov DWORD PTR [esi+4], eax
	add esi, 4
	add ecx, 4
	cmp ecx, ebp
	je 28f
	jmp 29f
28:
	mov ecx, 0
29:
	mov DWORD PTR [edi+276], ecx
	mov DWORD PTR [edi+280], ebp
	sub edx, 1
	mov DWORD PTR [edi+284], edx
	jne 21b
	mov ebx, DWORD PTR [edi+256]
	mov esi, DWORD PTR [edi+260]
	mov ebp, DWORD PTR [edi+268]
	mov edi, DWORD PTR [edi+264]
	ret
	.p2align 6
