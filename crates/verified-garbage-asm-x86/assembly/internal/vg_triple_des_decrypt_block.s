// The functions of `src/internal/vg_triple_des_decrypt_block.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_decrypt_block:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov ebp, eax
	mov edx, DWORD PTR [esp+8]
	mov edi, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	bswap edi
	bswap esi
	mov eax, 0
	mov ebx, 0
	mov ecx, esi
	shr ecx, 6
	and ecx, 1
	ror ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 2
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 3
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 30
	and ecx, 1
	ror ecx, 4
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 5
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 6
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 7
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 30
	and ecx, 1
	ror ecx, 8
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 9
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 10
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 11
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 28
	and ecx, 1
	ror ecx, 12
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 13
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 14
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 15
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 28
	and ecx, 1
	ror ecx, 16
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 10
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 2
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 18
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, esi
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 8
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 16
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 24
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, edi
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 8
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 16
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 24
	and ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	ror ecx, 1
	xor eax, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 2
	xor eax, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 3
	xor eax, ecx
	mov ecx, esi
	shr ecx, 31
	and ecx, 1
	ror ecx, 4
	xor eax, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, edi
	shr ecx, 31
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, esi
	shr ecx, 29
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, edi
	shr ecx, 13
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, edi
	shr ecx, 21
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, edi
	shr ecx, 29
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, esi
	shr ecx, 3
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, esi
	shr ecx, 19
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	xor eax, ecx
	mov esi, ebx
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	add eax, 376
	mov DWORD PTR [ebp+16], eax
	mov eax, 16
	mov DWORD PTR [ebp+20], eax
20:
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 27
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 10
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 28
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 11
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 29
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 12
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 30
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 13
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 31
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 14
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 15
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, eax
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+80]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+64]
	xor edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, edx
	xor eax, ecx
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+96], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, edx
	xor ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+80]
	and ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+100], edx
	mov edx, ecx
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, edx
	mov DWORD PTR [ebp+108], edx
	mov edx, ecx
	xor edx, ebx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, DWORD PTR [ebp+88]
	xor ecx, -1
	mov DWORD PTR [ebp+116], eax
	mov eax, ecx
	xor eax, ebx
	mov DWORD PTR [ebp+120], ebx
	mov ebx, DWORD PTR [ebp+84]
	and ebx, eax
	xor edx, ebx
	and edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+116]
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, ebx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+104]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+100]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+104]
	xor eax, DWORD PTR [ebp+112]
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	and eax, DWORD PTR [ebp+68]
	xor eax, edx
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+84]
	and ecx, eax
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+88]
	xor ecx, -1
	mov DWORD PTR [ebp+136], edx
	mov edx, ecx
	xor edx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+96]
	and ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+96], eax
	mov eax, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	xor ecx, DWORD PTR [ebp+96]
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+100]
	xor eax, edx
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+72]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+140]
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+96]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+136]
	and ebx, DWORD PTR [ebp+84]
	xor eax, ebx
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+96]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+140]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+88]
	xor eax, -1
	xor eax, DWORD PTR [ebp+68]
	mov ebx, DWORD PTR [ebp+120]
	xor ebx, DWORD PTR [ebp+88]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+84]
	xor ebx, eax
	mov edx, DWORD PTR [ebp+116]
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+128]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	and eax, DWORD PTR [ebp+76]
	xor edx, eax
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 31
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 23
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 17
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 9
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 23
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 4
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 24
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 5
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 25
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 6
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 26
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 7
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 27
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 8
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 28
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 9
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+64]
	and edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+96], ecx
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+104], ecx
	mov ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor edx, ecx
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ebx
	mov DWORD PTR [ebp+120], ebx
	mov ebx, ecx
	xor ebx, eax
	mov DWORD PTR [ebp+124], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, eax
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+116]
	xor ebx, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+136], ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+72]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+136]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	xor edx, ecx
	xor eax, DWORD PTR [ebp+120]
	and eax, DWORD PTR [ebp+80]
	xor edx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+112]
	and eax, DWORD PTR [ebp+76]
	xor edx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+80]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+128]
	xor ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+80]
	and ecx, DWORD PTR [ebp+84]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+80]
	mov ebx, DWORD PTR [ebp+104]
	xor ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+80]
	xor ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, ebx
	mov DWORD PTR [ebp+88], edx
	mov edx, DWORD PTR [ebp+104]
	xor edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+80]
	xor ecx, edx
	and ebx, DWORD PTR [ebp+76]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+72]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+108]
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+124]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+128]
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+76]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+116]
	xor ebx, DWORD PTR [ebp+112]
	mov edx, ebx
	xor edx, DWORD PTR [ebp+100]
	xor edx, -1
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 18
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 2
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 28
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 13
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 19
	mov ecx, DWORD PTR [edx]
	shr ecx, 30
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 20
	mov ecx, DWORD PTR [edx]
	shr ecx, 31
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 21
	mov ecx, DWORD PTR [edx+4]
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 22
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 1
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 23
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 2
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 24
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 3
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+80]
	and edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+80]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+96], eax
	mov eax, ecx
	xor eax, edx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, eax
	mov DWORD PTR [ebp+104], edx
	mov edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+108], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], eax
	mov eax, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, eax
	xor ebx, edx
	mov DWORD PTR [ebp+120], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+104]
	xor eax, edx
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+84]
	mov edx, DWORD PTR [ebp+88]
	xor edx, eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+100]
	xor edx, eax
	and ecx, DWORD PTR [ebp+76]
	xor edx, ecx
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+80]
	mov ecx, edx
	xor ecx, DWORD PTR [ebp+112]
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+96]
	xor eax, -1
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+92]
	xor ebx, eax
	mov DWORD PTR [ebp+124], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, ebx
	mov DWORD PTR [ebp+128], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+132], edx
	mov edx, DWORD PTR [ebp+80]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, edx
	mov DWORD PTR [ebp+140], edx
	mov edx, DWORD PTR [ebp+80]
	xor edx, eax
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+68]
	xor edx, ecx
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+120]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	mov ecx, DWORD PTR [ebp+148]
	xor ecx, DWORD PTR [ebp+96]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+68]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+108]
	xor ecx, DWORD PTR [ebp+96]
	xor ecx, -1
	mov DWORD PTR [ebp+148], ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, ecx
	mov DWORD PTR [ebp+120], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, ebx
	mov DWORD PTR [ebp+100], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+68]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+76]
	xor edx, ecx
	and edx, DWORD PTR [ebp+72]
	xor edx, DWORD PTR [ebp+148]
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	and edx, DWORD PTR [ebp+68]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+132]
	and edx, DWORD PTR [ebp+76]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+92]
	xor edx, DWORD PTR [ebp+144]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+88]
	xor ebx, DWORD PTR [ebp+92]
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	and edx, DWORD PTR [ebp+72]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+68]
	mov ebx, DWORD PTR [ebp+124]
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+140]
	and ebx, DWORD PTR [ebp+68]
	xor ebx, DWORD PTR [ebp+104]
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+108]
	xor ebx, eax
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+120]
	xor ecx, DWORD PTR [ebp+100]
	and ecx, DWORD PTR [ebp+68]
	xor ebx, ecx
	and eax, DWORD PTR [ebp+68]
	xor eax, DWORD PTR [ebp+120]
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+72]
	xor edx, ebx
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 6
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 30
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 16
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 24
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 15
	mov ecx, DWORD PTR [edx]
	shr ecx, 24
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 16
	mov ecx, DWORD PTR [edx]
	shr ecx, 25
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 17
	mov ecx, DWORD PTR [edx]
	shr ecx, 26
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 18
	mov ecx, DWORD PTR [edx]
	shr ecx, 27
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 19
	mov ecx, DWORD PTR [edx]
	shr ecx, 28
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 20
	mov ecx, DWORD PTR [edx]
	shr ecx, 29
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+84]
	and edx, ebx
	mov DWORD PTR [ebp+96], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+100], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+104], ecx
	mov ecx, edx
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, ecx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, edx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+68]
	xor edx, eax
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+80]
	and eax, edx
	mov DWORD PTR [ebp+124], edx
	mov edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor edx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+108]
	xor eax, -1
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+88], ecx
	mov ecx, DWORD PTR [ebp+84]
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+116]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, edx
	xor eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, eax
	mov DWORD PTR [ebp+112], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+108]
	xor eax, -1
	and eax, DWORD PTR [ebp+80]
	xor eax, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, DWORD PTR [ebp+120]
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+72]
	xor eax, ebx
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	and edx, DWORD PTR [ebp+64]
	xor eax, edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+140]
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+104]
	xor edx, ebx
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+72]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	mov ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+80]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, DWORD PTR [ebp+116]
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, ecx
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+64]
	xor ebx, ecx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 1
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 10
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 20
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 26
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 11
	mov ecx, DWORD PTR [edx]
	shr ecx, 18
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 12
	mov ecx, DWORD PTR [edx]
	shr ecx, 19
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 13
	mov ecx, DWORD PTR [edx]
	shr ecx, 20
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 14
	mov ecx, DWORD PTR [edx]
	shr ecx, 21
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 15
	mov ecx, DWORD PTR [edx]
	shr ecx, 22
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 16
	mov ecx, DWORD PTR [edx]
	shr ecx, 23
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, eax
	xor ecx, -1
	mov edx, ecx
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ecx
	mov ecx, ebx
	xor ecx, edx
	mov DWORD PTR [ebp+92], ebx
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+96], edx
	mov edx, ebx
	and edx, ecx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, edx
	mov DWORD PTR [ebp+104], edx
	mov edx, DWORD PTR [ebp+84]
	xor edx, eax
	xor edx, -1
	mov DWORD PTR [ebp+108], ebx
	mov ebx, DWORD PTR [ebp+88]
	and ebx, edx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, edx
	xor ecx, ebx
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+80]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+120], eax
	mov eax, ebx
	and eax, ecx
	xor eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+124], ecx
	mov ecx, edx
	xor ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+128], edx
	mov edx, ebx
	and edx, ecx
	xor edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+72]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and edx, ecx
	xor eax, edx
	mov edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+84]
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+96]
	xor ecx, eax
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+108]
	and eax, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and edx, ecx
	xor edx, DWORD PTR [ebp+136]
	mov eax, DWORD PTR [ebp+108]
	and eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+136], edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+120]
	xor eax, -1
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, eax
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, ecx
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], edx
	mov edx, ebx
	and edx, ecx
	xor eax, edx
	and eax, DWORD PTR [ebp+140]
	xor eax, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+132]
	and ecx, ebx
	xor ecx, DWORD PTR [ebp+76]
	mov edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, edx
	mov DWORD PTR [ebp+128], edx
	mov edx, ebx
	and edx, eax
	xor edx, DWORD PTR [ebp+92]
	and edx, DWORD PTR [ebp+140]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+148]
	xor ecx, DWORD PTR [ebp+116]
	mov edx, DWORD PTR [ebp+124]
	xor edx, DWORD PTR [ebp+108]
	xor edx, ebx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+152]
	xor ecx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+96]
	xor eax, DWORD PTR [ebp+92]
	and eax, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	mov eax, DWORD PTR [ebp+108]
	and eax, ecx
	mov DWORD PTR [ebp+152], ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor ecx, DWORD PTR [ebp+100]
	and ecx, DWORD PTR [ebp+148]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	and edx, DWORD PTR [ebp+112]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+132]
	xor edx, DWORD PTR [ebp+108]
	and edx, ebx
	xor edx, DWORD PTR [ebp+144]
	and edx, DWORD PTR [ebp+140]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+152]
	xor edx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+76]
	xor ecx, DWORD PTR [ebp+96]
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	xor ecx, eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+120]
	xor eax, -1
	and ebx, eax
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	and edx, DWORD PTR [ebp+148]
	xor edx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 3
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 25
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 14
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 8
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 7
	mov ecx, DWORD PTR [edx]
	shr ecx, 12
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 8
	mov ecx, DWORD PTR [edx]
	shr ecx, 13
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 9
	mov ecx, DWORD PTR [edx]
	shr ecx, 14
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 10
	mov ecx, DWORD PTR [edx]
	shr ecx, 15
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 11
	mov ecx, DWORD PTR [edx]
	shr ecx, 16
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 12
	mov ecx, DWORD PTR [edx]
	shr ecx, 17
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+76]
	and edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, edx
	xor ebx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, edx
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+100], eax
	mov eax, ecx
	xor eax, edx
	and eax, DWORD PTR [ebp+72]
	xor ebx, eax
	mov eax, edx
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov DWORD PTR [ebp+104], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+100]
	xor edx, -1
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, edx
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, ecx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+84]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+120], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, eax
	mov DWORD PTR [ebp+124], ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+76]
	and ebx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	xor ebx, edx
	and ebx, DWORD PTR [ebp+72]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+132]
	and ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, ebx
	mov DWORD PTR [ebp+140], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+88]
	xor eax, edx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+108]
	xor ebx, DWORD PTR [ebp+116]
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+84]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, DWORD PTR [ebp+68]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, edx
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	xor eax, ebx
	and eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+108]
	mov ebx, DWORD PTR [ebp+144]
	xor ebx, DWORD PTR [ebp+116]
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, DWORD PTR [ebp+104]
	and ecx, DWORD PTR [ebp+72]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+100]
	xor ecx, -1
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+136]
	xor eax, ecx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+140]
	xor eax, edx
	and eax, DWORD PTR [ebp+84]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+72]
	xor edx, ecx
	and edx, DWORD PTR [ebp+84]
	xor eax, edx
	and eax, DWORD PTR [ebp+64]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+68]
	xor eax, DWORD PTR [ebp+124]
	mov edx, DWORD PTR [ebp+84]
	and edx, DWORD PTR [ebp+120]
	xor eax, edx
	mov edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+116]
	and edx, DWORD PTR [ebp+72]
	xor edx, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+88]
	xor ecx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+92]
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+84]
	xor edx, ecx
	and edx, DWORD PTR [ebp+64]
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 19
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 11
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 29
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 4
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 3
	mov ecx, DWORD PTR [edx]
	shr ecx, 6
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 4
	mov ecx, DWORD PTR [edx]
	shr ecx, 7
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 5
	mov ecx, DWORD PTR [edx]
	shr ecx, 8
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 6
	mov ecx, DWORD PTR [edx]
	shr ecx, 9
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 7
	mov ecx, DWORD PTR [edx]
	shr ecx, 10
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 8
	mov ecx, DWORD PTR [edx]
	shr ecx, 11
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, DWORD PTR [ebp+64]
	mov edx, DWORD PTR [ebp+64]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, ecx
	xor edx, ebx
	mov DWORD PTR [ebp+96], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, ebx
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, eax
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+88]
	xor eax, ecx
	mov DWORD PTR [ebp+124], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, DWORD PTR [ebp+104]
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor edx, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, DWORD PTR [ebp+108]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+92]
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+68]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+72]
	mov eax, DWORD PTR [ebp+100]
	xor eax, DWORD PTR [ebp+112]
	xor eax, -1
	mov DWORD PTR [ebp+128], edx
	mov edx, eax
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, edx
	mov DWORD PTR [ebp+136], edx
	mov edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], eax
	mov eax, edx
	xor eax, DWORD PTR [ebp+124]
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+140], ebx
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+112]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+72]
	xor ebx, ecx
	xor ebx, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+144], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+68]
	xor ebx, DWORD PTR [ebp+140]
	xor edx, DWORD PTR [ebp+112]
	xor edx, -1
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+116]
	mov ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+76]
	and ebx, DWORD PTR [ebp+84]
	xor ecx, ebx
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], edx
	mov edx, DWORD PTR [ebp+104]
	xor edx, DWORD PTR [ebp+136]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+80]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, DWORD PTR [ebp+100]
	and ebx, DWORD PTR [ebp+76]
	xor ebx, DWORD PTR [ebp+88]
	mov edx, DWORD PTR [ebp+80]
	and edx, DWORD PTR [ebp+124]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+68]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+120]
	xor ebx, DWORD PTR [ebp+136]
	xor ebx, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+84]
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+144]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+76]
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+84]
	and edx, DWORD PTR [ebp+76]
	xor eax, edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor eax, edx
	and eax, DWORD PTR [ebp+68]
	xor ebx, eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 7
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 22
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 12
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 31
	mov ecx, DWORD PTR [edx]
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	mov ecx, DWORD PTR [edx]
	shr ecx, 1
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 1
	mov ecx, DWORD PTR [edx]
	shr ecx, 2
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 2
	mov ecx, DWORD PTR [edx]
	shr ecx, 3
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 3
	mov ecx, DWORD PTR [edx]
	shr ecx, 4
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 4
	mov ecx, DWORD PTR [edx]
	shr ecx, 5
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+64]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+84]
	xor edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+76]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+92], ecx
	mov ecx, edx
	xor ecx, ebx
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+68]
	xor edx, eax
	xor edx, -1
	xor ecx, edx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	and eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+108], ecx
	mov ecx, ebx
	and ecx, eax
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, ecx
	and ebx, edx
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	and ebx, ecx
	xor ebx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	mov DWORD PTR [ebp+120], ecx
	mov ecx, DWORD PTR [ebp+92]
	and ecx, ebx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, ebx
	xor ecx, DWORD PTR [ebp+108]
	and ecx, edx
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, eax
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+112]
	and eax, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, eax
	mov DWORD PTR [ebp+88], eax
	mov eax, edx
	and eax, DWORD PTR [ebp+124]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+120]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	and ecx, ebx
	xor ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+140], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+144], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+112]
	and ebx, ecx
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, ebx
	and ecx, edx
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+124], ebx
	mov ebx, edx
	and ebx, DWORD PTR [ebp+116]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+120]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+152], ecx
	mov ecx, ebx
	xor ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], eax
	mov eax, edx
	and eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+96], edx
	mov edx, ecx
	xor edx, eax
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+96]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+120]
	xor edx, ecx
	and edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+128]
	xor ecx, DWORD PTR [ebp+116]
	mov ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+144]
	xor ebx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+108], edx
	mov edx, DWORD PTR [ebp+96]
	and edx, ebx
	xor ecx, edx
	mov edx, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+120]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+140]
	and eax, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, DWORD PTR [ebp+136]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+96]
	and edx, DWORD PTR [ebp+152]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+132]
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+88]
	and eax, DWORD PTR [ebp+96]
	xor eax, edx
	and eax, DWORD PTR [ebp+120]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+104]
	xor edx, -1
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+96]
	and ecx, DWORD PTR [ebp+148]
	xor edx, ecx
	and edx, DWORD PTR [ebp+120]
	xor eax, edx
	and eax, DWORD PTR [ebp+136]
	xor ebx, eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 21
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 15
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 27
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 5
	xor esi, eax
	mov eax, esi
	mov esi, edi
	mov edi, eax
	mov eax, DWORD PTR [ebp+16]
	sub eax, 8
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	sub eax, 1
	mov DWORD PTR [ebp+20], eax
	jne 20b
	mov eax, esi
	mov esi, edi
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	add eax, 128
	mov DWORD PTR [ebp+16], eax
	mov eax, 16
	mov DWORD PTR [ebp+20], eax
21:
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 27
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 10
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 28
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 11
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 29
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 12
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 30
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 13
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 31
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 14
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 15
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, eax
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+80]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+64]
	xor edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, edx
	xor eax, ecx
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+96], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, edx
	xor ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+80]
	and ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+100], edx
	mov edx, ecx
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, edx
	mov DWORD PTR [ebp+108], edx
	mov edx, ecx
	xor edx, ebx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, DWORD PTR [ebp+88]
	xor ecx, -1
	mov DWORD PTR [ebp+116], eax
	mov eax, ecx
	xor eax, ebx
	mov DWORD PTR [ebp+120], ebx
	mov ebx, DWORD PTR [ebp+84]
	and ebx, eax
	xor edx, ebx
	and edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+116]
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, ebx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+104]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+100]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+104]
	xor eax, DWORD PTR [ebp+112]
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	and eax, DWORD PTR [ebp+68]
	xor eax, edx
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+84]
	and ecx, eax
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+88]
	xor ecx, -1
	mov DWORD PTR [ebp+136], edx
	mov edx, ecx
	xor edx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+96]
	and ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+96], eax
	mov eax, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	xor ecx, DWORD PTR [ebp+96]
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+100]
	xor eax, edx
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+72]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+140]
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+96]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+136]
	and ebx, DWORD PTR [ebp+84]
	xor eax, ebx
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+96]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+140]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+88]
	xor eax, -1
	xor eax, DWORD PTR [ebp+68]
	mov ebx, DWORD PTR [ebp+120]
	xor ebx, DWORD PTR [ebp+88]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+84]
	xor ebx, eax
	mov edx, DWORD PTR [ebp+116]
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+128]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	and eax, DWORD PTR [ebp+76]
	xor edx, eax
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 31
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 23
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 17
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 9
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 23
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 4
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 24
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 5
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 25
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 6
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 26
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 7
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 27
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 8
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 28
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 9
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+64]
	and edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+96], ecx
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+104], ecx
	mov ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor edx, ecx
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ebx
	mov DWORD PTR [ebp+120], ebx
	mov ebx, ecx
	xor ebx, eax
	mov DWORD PTR [ebp+124], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, eax
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+116]
	xor ebx, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+136], ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+72]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+136]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	xor edx, ecx
	xor eax, DWORD PTR [ebp+120]
	and eax, DWORD PTR [ebp+80]
	xor edx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+112]
	and eax, DWORD PTR [ebp+76]
	xor edx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+80]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+128]
	xor ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+80]
	and ecx, DWORD PTR [ebp+84]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+80]
	mov ebx, DWORD PTR [ebp+104]
	xor ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+80]
	xor ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, ebx
	mov DWORD PTR [ebp+88], edx
	mov edx, DWORD PTR [ebp+104]
	xor edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+80]
	xor ecx, edx
	and ebx, DWORD PTR [ebp+76]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+72]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+108]
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+124]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+128]
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+76]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+116]
	xor ebx, DWORD PTR [ebp+112]
	mov edx, ebx
	xor edx, DWORD PTR [ebp+100]
	xor edx, -1
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 18
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 2
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 28
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 13
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 19
	mov ecx, DWORD PTR [edx]
	shr ecx, 30
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 20
	mov ecx, DWORD PTR [edx]
	shr ecx, 31
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 21
	mov ecx, DWORD PTR [edx+4]
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 22
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 1
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 23
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 2
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 24
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 3
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+80]
	and edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+80]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+96], eax
	mov eax, ecx
	xor eax, edx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, eax
	mov DWORD PTR [ebp+104], edx
	mov edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+108], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], eax
	mov eax, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, eax
	xor ebx, edx
	mov DWORD PTR [ebp+120], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+104]
	xor eax, edx
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+84]
	mov edx, DWORD PTR [ebp+88]
	xor edx, eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+100]
	xor edx, eax
	and ecx, DWORD PTR [ebp+76]
	xor edx, ecx
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+80]
	mov ecx, edx
	xor ecx, DWORD PTR [ebp+112]
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+96]
	xor eax, -1
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+92]
	xor ebx, eax
	mov DWORD PTR [ebp+124], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, ebx
	mov DWORD PTR [ebp+128], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+132], edx
	mov edx, DWORD PTR [ebp+80]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, edx
	mov DWORD PTR [ebp+140], edx
	mov edx, DWORD PTR [ebp+80]
	xor edx, eax
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+68]
	xor edx, ecx
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+120]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	mov ecx, DWORD PTR [ebp+148]
	xor ecx, DWORD PTR [ebp+96]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+68]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+108]
	xor ecx, DWORD PTR [ebp+96]
	xor ecx, -1
	mov DWORD PTR [ebp+148], ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, ecx
	mov DWORD PTR [ebp+120], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, ebx
	mov DWORD PTR [ebp+100], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+68]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+76]
	xor edx, ecx
	and edx, DWORD PTR [ebp+72]
	xor edx, DWORD PTR [ebp+148]
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	and edx, DWORD PTR [ebp+68]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+132]
	and edx, DWORD PTR [ebp+76]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+92]
	xor edx, DWORD PTR [ebp+144]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+88]
	xor ebx, DWORD PTR [ebp+92]
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	and edx, DWORD PTR [ebp+72]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+68]
	mov ebx, DWORD PTR [ebp+124]
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+140]
	and ebx, DWORD PTR [ebp+68]
	xor ebx, DWORD PTR [ebp+104]
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+108]
	xor ebx, eax
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+120]
	xor ecx, DWORD PTR [ebp+100]
	and ecx, DWORD PTR [ebp+68]
	xor ebx, ecx
	and eax, DWORD PTR [ebp+68]
	xor eax, DWORD PTR [ebp+120]
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+72]
	xor edx, ebx
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 6
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 30
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 16
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 24
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 15
	mov ecx, DWORD PTR [edx]
	shr ecx, 24
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 16
	mov ecx, DWORD PTR [edx]
	shr ecx, 25
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 17
	mov ecx, DWORD PTR [edx]
	shr ecx, 26
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 18
	mov ecx, DWORD PTR [edx]
	shr ecx, 27
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 19
	mov ecx, DWORD PTR [edx]
	shr ecx, 28
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 20
	mov ecx, DWORD PTR [edx]
	shr ecx, 29
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+84]
	and edx, ebx
	mov DWORD PTR [ebp+96], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+100], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+104], ecx
	mov ecx, edx
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, ecx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, edx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+68]
	xor edx, eax
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+80]
	and eax, edx
	mov DWORD PTR [ebp+124], edx
	mov edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor edx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+108]
	xor eax, -1
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+88], ecx
	mov ecx, DWORD PTR [ebp+84]
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+116]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, edx
	xor eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, eax
	mov DWORD PTR [ebp+112], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+108]
	xor eax, -1
	and eax, DWORD PTR [ebp+80]
	xor eax, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, DWORD PTR [ebp+120]
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+72]
	xor eax, ebx
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	and edx, DWORD PTR [ebp+64]
	xor eax, edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+140]
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+104]
	xor edx, ebx
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+72]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	mov ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+80]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, DWORD PTR [ebp+116]
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, ecx
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+64]
	xor ebx, ecx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 1
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 10
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 20
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 26
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 11
	mov ecx, DWORD PTR [edx]
	shr ecx, 18
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 12
	mov ecx, DWORD PTR [edx]
	shr ecx, 19
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 13
	mov ecx, DWORD PTR [edx]
	shr ecx, 20
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 14
	mov ecx, DWORD PTR [edx]
	shr ecx, 21
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 15
	mov ecx, DWORD PTR [edx]
	shr ecx, 22
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 16
	mov ecx, DWORD PTR [edx]
	shr ecx, 23
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, eax
	xor ecx, -1
	mov edx, ecx
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ecx
	mov ecx, ebx
	xor ecx, edx
	mov DWORD PTR [ebp+92], ebx
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+96], edx
	mov edx, ebx
	and edx, ecx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, edx
	mov DWORD PTR [ebp+104], edx
	mov edx, DWORD PTR [ebp+84]
	xor edx, eax
	xor edx, -1
	mov DWORD PTR [ebp+108], ebx
	mov ebx, DWORD PTR [ebp+88]
	and ebx, edx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, edx
	xor ecx, ebx
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+80]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+120], eax
	mov eax, ebx
	and eax, ecx
	xor eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+124], ecx
	mov ecx, edx
	xor ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+128], edx
	mov edx, ebx
	and edx, ecx
	xor edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+72]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and edx, ecx
	xor eax, edx
	mov edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+84]
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+96]
	xor ecx, eax
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+108]
	and eax, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and edx, ecx
	xor edx, DWORD PTR [ebp+136]
	mov eax, DWORD PTR [ebp+108]
	and eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+136], edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+120]
	xor eax, -1
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, eax
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, ecx
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], edx
	mov edx, ebx
	and edx, ecx
	xor eax, edx
	and eax, DWORD PTR [ebp+140]
	xor eax, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+132]
	and ecx, ebx
	xor ecx, DWORD PTR [ebp+76]
	mov edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, edx
	mov DWORD PTR [ebp+128], edx
	mov edx, ebx
	and edx, eax
	xor edx, DWORD PTR [ebp+92]
	and edx, DWORD PTR [ebp+140]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+148]
	xor ecx, DWORD PTR [ebp+116]
	mov edx, DWORD PTR [ebp+124]
	xor edx, DWORD PTR [ebp+108]
	xor edx, ebx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+152]
	xor ecx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+96]
	xor eax, DWORD PTR [ebp+92]
	and eax, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	mov eax, DWORD PTR [ebp+108]
	and eax, ecx
	mov DWORD PTR [ebp+152], ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor ecx, DWORD PTR [ebp+100]
	and ecx, DWORD PTR [ebp+148]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	and edx, DWORD PTR [ebp+112]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+132]
	xor edx, DWORD PTR [ebp+108]
	and edx, ebx
	xor edx, DWORD PTR [ebp+144]
	and edx, DWORD PTR [ebp+140]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+152]
	xor edx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+76]
	xor ecx, DWORD PTR [ebp+96]
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	xor ecx, eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+120]
	xor eax, -1
	and ebx, eax
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	and edx, DWORD PTR [ebp+148]
	xor edx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 3
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 25
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 14
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 8
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 7
	mov ecx, DWORD PTR [edx]
	shr ecx, 12
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 8
	mov ecx, DWORD PTR [edx]
	shr ecx, 13
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 9
	mov ecx, DWORD PTR [edx]
	shr ecx, 14
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 10
	mov ecx, DWORD PTR [edx]
	shr ecx, 15
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 11
	mov ecx, DWORD PTR [edx]
	shr ecx, 16
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 12
	mov ecx, DWORD PTR [edx]
	shr ecx, 17
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+76]
	and edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, edx
	xor ebx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, edx
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+100], eax
	mov eax, ecx
	xor eax, edx
	and eax, DWORD PTR [ebp+72]
	xor ebx, eax
	mov eax, edx
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov DWORD PTR [ebp+104], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+100]
	xor edx, -1
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, edx
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, ecx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+84]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+120], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, eax
	mov DWORD PTR [ebp+124], ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+76]
	and ebx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	xor ebx, edx
	and ebx, DWORD PTR [ebp+72]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+132]
	and ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, ebx
	mov DWORD PTR [ebp+140], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+88]
	xor eax, edx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+108]
	xor ebx, DWORD PTR [ebp+116]
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+84]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, DWORD PTR [ebp+68]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, edx
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	xor eax, ebx
	and eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+108]
	mov ebx, DWORD PTR [ebp+144]
	xor ebx, DWORD PTR [ebp+116]
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, DWORD PTR [ebp+104]
	and ecx, DWORD PTR [ebp+72]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+100]
	xor ecx, -1
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+136]
	xor eax, ecx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+140]
	xor eax, edx
	and eax, DWORD PTR [ebp+84]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+72]
	xor edx, ecx
	and edx, DWORD PTR [ebp+84]
	xor eax, edx
	and eax, DWORD PTR [ebp+64]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+68]
	xor eax, DWORD PTR [ebp+124]
	mov edx, DWORD PTR [ebp+84]
	and edx, DWORD PTR [ebp+120]
	xor eax, edx
	mov edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+116]
	and edx, DWORD PTR [ebp+72]
	xor edx, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+88]
	xor ecx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+92]
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+84]
	xor edx, ecx
	and edx, DWORD PTR [ebp+64]
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 19
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 11
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 29
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 4
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 3
	mov ecx, DWORD PTR [edx]
	shr ecx, 6
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 4
	mov ecx, DWORD PTR [edx]
	shr ecx, 7
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 5
	mov ecx, DWORD PTR [edx]
	shr ecx, 8
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 6
	mov ecx, DWORD PTR [edx]
	shr ecx, 9
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 7
	mov ecx, DWORD PTR [edx]
	shr ecx, 10
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 8
	mov ecx, DWORD PTR [edx]
	shr ecx, 11
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, DWORD PTR [ebp+64]
	mov edx, DWORD PTR [ebp+64]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, ecx
	xor edx, ebx
	mov DWORD PTR [ebp+96], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, ebx
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, eax
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+88]
	xor eax, ecx
	mov DWORD PTR [ebp+124], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, DWORD PTR [ebp+104]
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor edx, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, DWORD PTR [ebp+108]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+92]
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+68]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+72]
	mov eax, DWORD PTR [ebp+100]
	xor eax, DWORD PTR [ebp+112]
	xor eax, -1
	mov DWORD PTR [ebp+128], edx
	mov edx, eax
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, edx
	mov DWORD PTR [ebp+136], edx
	mov edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], eax
	mov eax, edx
	xor eax, DWORD PTR [ebp+124]
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+140], ebx
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+112]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+72]
	xor ebx, ecx
	xor ebx, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+144], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+68]
	xor ebx, DWORD PTR [ebp+140]
	xor edx, DWORD PTR [ebp+112]
	xor edx, -1
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+116]
	mov ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+76]
	and ebx, DWORD PTR [ebp+84]
	xor ecx, ebx
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], edx
	mov edx, DWORD PTR [ebp+104]
	xor edx, DWORD PTR [ebp+136]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+80]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, DWORD PTR [ebp+100]
	and ebx, DWORD PTR [ebp+76]
	xor ebx, DWORD PTR [ebp+88]
	mov edx, DWORD PTR [ebp+80]
	and edx, DWORD PTR [ebp+124]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+68]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+120]
	xor ebx, DWORD PTR [ebp+136]
	xor ebx, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+84]
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+144]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+76]
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+84]
	and edx, DWORD PTR [ebp+76]
	xor eax, edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor eax, edx
	and eax, DWORD PTR [ebp+68]
	xor ebx, eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 7
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 22
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 12
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 31
	mov ecx, DWORD PTR [edx]
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	mov ecx, DWORD PTR [edx]
	shr ecx, 1
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 1
	mov ecx, DWORD PTR [edx]
	shr ecx, 2
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 2
	mov ecx, DWORD PTR [edx]
	shr ecx, 3
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 3
	mov ecx, DWORD PTR [edx]
	shr ecx, 4
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 4
	mov ecx, DWORD PTR [edx]
	shr ecx, 5
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+64]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+84]
	xor edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+76]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+92], ecx
	mov ecx, edx
	xor ecx, ebx
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+68]
	xor edx, eax
	xor edx, -1
	xor ecx, edx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	and eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+108], ecx
	mov ecx, ebx
	and ecx, eax
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, ecx
	and ebx, edx
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	and ebx, ecx
	xor ebx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	mov DWORD PTR [ebp+120], ecx
	mov ecx, DWORD PTR [ebp+92]
	and ecx, ebx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, ebx
	xor ecx, DWORD PTR [ebp+108]
	and ecx, edx
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, eax
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+112]
	and eax, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, eax
	mov DWORD PTR [ebp+88], eax
	mov eax, edx
	and eax, DWORD PTR [ebp+124]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+120]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	and ecx, ebx
	xor ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+140], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+144], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+112]
	and ebx, ecx
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, ebx
	and ecx, edx
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+124], ebx
	mov ebx, edx
	and ebx, DWORD PTR [ebp+116]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+120]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+152], ecx
	mov ecx, ebx
	xor ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], eax
	mov eax, edx
	and eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+96], edx
	mov edx, ecx
	xor edx, eax
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+96]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+120]
	xor edx, ecx
	and edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+128]
	xor ecx, DWORD PTR [ebp+116]
	mov ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+144]
	xor ebx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+108], edx
	mov edx, DWORD PTR [ebp+96]
	and edx, ebx
	xor ecx, edx
	mov edx, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+120]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+140]
	and eax, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, DWORD PTR [ebp+136]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+96]
	and edx, DWORD PTR [ebp+152]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+132]
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+88]
	and eax, DWORD PTR [ebp+96]
	xor eax, edx
	and eax, DWORD PTR [ebp+120]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+104]
	xor edx, -1
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+96]
	and ecx, DWORD PTR [ebp+148]
	xor edx, ecx
	and edx, DWORD PTR [ebp+120]
	xor eax, edx
	and eax, DWORD PTR [ebp+136]
	xor ebx, eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 21
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 15
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 27
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 5
	xor esi, eax
	mov eax, esi
	mov esi, edi
	mov edi, eax
	mov eax, DWORD PTR [ebp+16]
	add eax, 8
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	sub eax, 1
	mov DWORD PTR [ebp+20], eax
	jne 21b
	mov eax, esi
	mov esi, edi
	mov edi, eax
	mov eax, DWORD PTR [esp+4]
	add eax, 120
	mov DWORD PTR [ebp+16], eax
	mov eax, 16
	mov DWORD PTR [ebp+20], eax
22:
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 27
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 10
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 28
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 11
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 29
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 12
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 30
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 13
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 31
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 14
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 15
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, eax
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+80]
	and ecx, ebx
	mov edx, DWORD PTR [ebp+64]
	xor edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, edx
	xor eax, ecx
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+96], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, edx
	xor ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+80]
	and ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+100], edx
	mov edx, ecx
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, edx
	mov DWORD PTR [ebp+108], edx
	mov edx, ecx
	xor edx, ebx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, DWORD PTR [ebp+88]
	xor ecx, -1
	mov DWORD PTR [ebp+116], eax
	mov eax, ecx
	xor eax, ebx
	mov DWORD PTR [ebp+120], ebx
	mov ebx, DWORD PTR [ebp+84]
	and ebx, eax
	xor edx, ebx
	and edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+116]
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, ebx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+104]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+100]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+104]
	xor eax, DWORD PTR [ebp+112]
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	and eax, DWORD PTR [ebp+68]
	xor eax, edx
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+84]
	and ecx, eax
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+88]
	xor ecx, -1
	mov DWORD PTR [ebp+136], edx
	mov edx, ecx
	xor edx, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+96]
	and ecx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+96], eax
	mov eax, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	xor ecx, DWORD PTR [ebp+96]
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, eax
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+140], eax
	mov eax, DWORD PTR [ebp+100]
	xor eax, edx
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+72]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+140]
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+96]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+136]
	and ebx, DWORD PTR [ebp+84]
	xor eax, ebx
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+120]
	xor eax, DWORD PTR [ebp+96]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+140]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor ecx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+88]
	xor eax, -1
	xor eax, DWORD PTR [ebp+68]
	mov ebx, DWORD PTR [ebp+120]
	xor ebx, DWORD PTR [ebp+88]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+84]
	xor ebx, eax
	mov edx, DWORD PTR [ebp+116]
	xor edx, DWORD PTR [ebp+88]
	xor edx, -1
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+128]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+84]
	xor eax, ecx
	and eax, DWORD PTR [ebp+76]
	xor edx, eax
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 31
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 23
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 17
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 9
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 23
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 4
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 24
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 5
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 25
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 6
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 26
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 7
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 27
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 8
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 28
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 9
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+64]
	and edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+96], ecx
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+104], ecx
	mov ecx, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor edx, ecx
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, eax
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ebx
	mov DWORD PTR [ebp+120], ebx
	mov ebx, ecx
	xor ebx, eax
	mov DWORD PTR [ebp+124], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, eax
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+116]
	xor ebx, DWORD PTR [ebp+88]
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+136], ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+72]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+136]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	xor edx, ecx
	xor eax, DWORD PTR [ebp+120]
	and eax, DWORD PTR [ebp+80]
	xor edx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+112]
	and eax, DWORD PTR [ebp+76]
	xor edx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+80]
	xor eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+128]
	xor ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, DWORD PTR [ebp+80]
	and ecx, DWORD PTR [ebp+84]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+80]
	mov ebx, DWORD PTR [ebp+104]
	xor ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+80]
	xor ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+76]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, ebx
	mov DWORD PTR [ebp+88], edx
	mov edx, DWORD PTR [ebp+104]
	xor edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+80]
	xor ecx, edx
	and ebx, DWORD PTR [ebp+76]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+72]
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+108]
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+124]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+128]
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+76]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+116]
	xor ebx, DWORD PTR [ebp+112]
	mov edx, ebx
	xor edx, DWORD PTR [ebp+100]
	xor edx, -1
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	mov DWORD PTR [ebp+72], eax
	mov DWORD PTR [ebp+76], ecx
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 18
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 2
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 28
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 13
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 19
	mov ecx, DWORD PTR [edx]
	shr ecx, 30
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 20
	mov ecx, DWORD PTR [edx]
	shr ecx, 31
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 21
	mov ecx, DWORD PTR [edx+4]
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 22
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 1
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 23
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 2
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 24
	mov ecx, DWORD PTR [edx+4]
	shr ecx, 3
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+80]
	and edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+80]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+96], eax
	mov eax, ecx
	xor eax, edx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, eax
	mov DWORD PTR [ebp+104], edx
	mov edx, ebx
	xor edx, ecx
	mov DWORD PTR [ebp+108], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	mov DWORD PTR [ebp+112], ecx
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], eax
	mov eax, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, eax
	xor ebx, edx
	mov DWORD PTR [ebp+120], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+104]
	xor eax, edx
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+84]
	mov edx, DWORD PTR [ebp+88]
	xor edx, eax
	mov DWORD PTR [ebp+88], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+100]
	xor edx, eax
	and ecx, DWORD PTR [ebp+76]
	xor edx, ecx
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+80]
	mov ecx, edx
	xor ecx, DWORD PTR [ebp+112]
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+96]
	xor eax, -1
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, DWORD PTR [ebp+92]
	xor ebx, eax
	mov DWORD PTR [ebp+124], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, ebx
	mov DWORD PTR [ebp+128], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+132], edx
	mov edx, DWORD PTR [ebp+80]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, edx
	mov DWORD PTR [ebp+140], edx
	mov edx, DWORD PTR [ebp+80]
	xor edx, eax
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+100]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+68]
	xor edx, ecx
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+120]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	mov ecx, DWORD PTR [ebp+148]
	xor ecx, DWORD PTR [ebp+96]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+68]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+108]
	xor ecx, DWORD PTR [ebp+96]
	xor ecx, -1
	mov DWORD PTR [ebp+148], ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, ecx
	mov DWORD PTR [ebp+120], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, ebx
	mov DWORD PTR [ebp+100], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+68]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+76]
	xor edx, ecx
	and edx, DWORD PTR [ebp+72]
	xor edx, DWORD PTR [ebp+148]
	mov ecx, DWORD PTR [ebp+64]
	and ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+96]
	xor edx, -1
	and edx, DWORD PTR [ebp+68]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+132]
	and edx, DWORD PTR [ebp+76]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+92]
	xor edx, DWORD PTR [ebp+144]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+88]
	xor ebx, DWORD PTR [ebp+92]
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	and edx, DWORD PTR [ebp+72]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+68]
	mov ebx, DWORD PTR [ebp+124]
	xor ebx, DWORD PTR [ebp+96]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+140]
	and ebx, DWORD PTR [ebp+68]
	xor ebx, DWORD PTR [ebp+104]
	and ebx, DWORD PTR [ebp+76]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+108]
	xor ebx, eax
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+120]
	xor ecx, DWORD PTR [ebp+100]
	and ecx, DWORD PTR [ebp+68]
	xor ebx, ecx
	and eax, DWORD PTR [ebp+68]
	xor eax, DWORD PTR [ebp+120]
	and eax, DWORD PTR [ebp+76]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+72]
	xor edx, ebx
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 6
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 30
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 16
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 24
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 15
	mov ecx, DWORD PTR [edx]
	shr ecx, 24
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 16
	mov ecx, DWORD PTR [edx]
	shr ecx, 25
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 17
	mov ecx, DWORD PTR [edx]
	shr ecx, 26
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 18
	mov ecx, DWORD PTR [edx]
	shr ecx, 27
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 19
	mov ecx, DWORD PTR [edx]
	shr ecx, 28
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 20
	mov ecx, DWORD PTR [edx]
	shr ecx, 29
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+84]
	and edx, ebx
	mov DWORD PTR [ebp+96], ebx
	mov ebx, ecx
	xor ebx, edx
	mov DWORD PTR [ebp+100], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+104], ecx
	mov ecx, edx
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+108], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, ecx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, edx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+68]
	xor edx, eax
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+80]
	and eax, edx
	mov DWORD PTR [ebp+124], edx
	mov edx, ecx
	xor edx, eax
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	and edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor edx, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+108]
	xor eax, -1
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+88], ecx
	mov ecx, DWORD PTR [ebp+84]
	and ecx, ebx
	xor eax, ecx
	mov DWORD PTR [ebp+132], ebx
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+116]
	xor eax, ebx
	and eax, DWORD PTR [ebp+72]
	xor edx, eax
	mov eax, DWORD PTR [ebp+64]
	and eax, edx
	xor eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], eax
	mov eax, DWORD PTR [ebp+84]
	and eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, eax
	mov DWORD PTR [ebp+112], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+108]
	xor eax, -1
	and eax, DWORD PTR [ebp+80]
	xor eax, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, DWORD PTR [ebp+120]
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+72]
	xor eax, ebx
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	and edx, DWORD PTR [ebp+64]
	xor eax, edx
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+140]
	mov ebx, DWORD PTR [ebp+80]
	and ebx, DWORD PTR [ebp+104]
	xor edx, ebx
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+72]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	mov ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+80]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, DWORD PTR [ebp+116]
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+64]
	and ebx, ecx
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+116], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, DWORD PTR [ebp+108]
	xor edx, -1
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	xor ecx, DWORD PTR [ebp+108]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+64]
	xor ebx, ecx
	mov DWORD PTR [ebp+68], eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 1
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 10
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 20
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 26
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 11
	mov ecx, DWORD PTR [edx]
	shr ecx, 18
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 12
	mov ecx, DWORD PTR [edx]
	shr ecx, 19
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 13
	mov ecx, DWORD PTR [edx]
	shr ecx, 20
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 14
	mov ecx, DWORD PTR [edx]
	shr ecx, 21
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 15
	mov ecx, DWORD PTR [edx]
	shr ecx, 22
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 16
	mov ecx, DWORD PTR [edx]
	shr ecx, 23
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+76]
	xor ecx, eax
	xor ecx, -1
	mov edx, ecx
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ecx
	mov ecx, ebx
	xor ecx, edx
	mov DWORD PTR [ebp+92], ebx
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+96], edx
	mov edx, ebx
	and edx, ecx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, edx
	mov DWORD PTR [ebp+104], edx
	mov edx, DWORD PTR [ebp+84]
	xor edx, eax
	xor edx, -1
	mov DWORD PTR [ebp+108], ebx
	mov ebx, DWORD PTR [ebp+88]
	and ebx, edx
	mov DWORD PTR [ebp+112], ecx
	mov ecx, edx
	xor ecx, ebx
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+80]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+120], eax
	mov eax, ebx
	and eax, ecx
	xor eax, DWORD PTR [ebp+112]
	mov DWORD PTR [ebp+124], ecx
	mov ecx, edx
	xor ecx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+128], edx
	mov edx, ebx
	and edx, ecx
	xor edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+72]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and edx, ecx
	xor eax, edx
	mov edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+136], eax
	mov eax, DWORD PTR [ebp+84]
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+140], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+96]
	xor ecx, eax
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+108]
	and eax, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+68]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	and edx, ecx
	xor edx, DWORD PTR [ebp+136]
	mov eax, DWORD PTR [ebp+108]
	and eax, DWORD PTR [ebp+124]
	mov DWORD PTR [ebp+136], edx
	mov edx, DWORD PTR [ebp+100]
	xor edx, eax
	xor edx, ebx
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+120]
	xor eax, -1
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, eax
	mov DWORD PTR [ebp+152], eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, ecx
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+116], edx
	mov edx, ebx
	and edx, ecx
	xor eax, edx
	and eax, DWORD PTR [ebp+140]
	xor eax, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+132]
	and ecx, ebx
	xor ecx, DWORD PTR [ebp+76]
	mov edx, DWORD PTR [ebp+108]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+116], eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, edx
	mov DWORD PTR [ebp+128], edx
	mov edx, ebx
	and edx, eax
	xor edx, DWORD PTR [ebp+92]
	and edx, DWORD PTR [ebp+140]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+148]
	xor ecx, DWORD PTR [ebp+116]
	mov edx, DWORD PTR [ebp+124]
	xor edx, DWORD PTR [ebp+108]
	xor edx, ebx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+152]
	xor ecx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+96]
	xor eax, DWORD PTR [ebp+92]
	and eax, ebx
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	mov eax, DWORD PTR [ebp+108]
	and eax, ecx
	mov DWORD PTR [ebp+152], ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+140]
	xor ecx, DWORD PTR [ebp+100]
	and ecx, DWORD PTR [ebp+148]
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], edx
	mov edx, ebx
	and edx, DWORD PTR [ebp+112]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+132]
	xor edx, DWORD PTR [ebp+108]
	and edx, ebx
	xor edx, DWORD PTR [ebp+144]
	and edx, DWORD PTR [ebp+140]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+152]
	xor edx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+108]
	and ecx, DWORD PTR [ebp+76]
	xor ecx, DWORD PTR [ebp+96]
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+120]
	xor ecx, -1
	xor ecx, eax
	mov eax, DWORD PTR [ebp+128]
	xor eax, DWORD PTR [ebp+120]
	xor eax, -1
	and ebx, eax
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+140]
	xor edx, ecx
	and edx, DWORD PTR [ebp+148]
	xor edx, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+136]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 3
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 25
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 14
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 8
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 7
	mov ecx, DWORD PTR [edx]
	shr ecx, 12
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 8
	mov ecx, DWORD PTR [edx]
	shr ecx, 13
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 9
	mov ecx, DWORD PTR [edx]
	shr ecx, 14
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 10
	mov ecx, DWORD PTR [edx]
	shr ecx, 15
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 11
	mov ecx, DWORD PTR [edx]
	shr ecx, 16
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 12
	mov ecx, DWORD PTR [edx]
	shr ecx, 17
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+76]
	and edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, edx
	xor ebx, DWORD PTR [ebp+68]
	mov DWORD PTR [ebp+92], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, edx
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+100], eax
	mov eax, ecx
	xor eax, edx
	and eax, DWORD PTR [ebp+72]
	xor ebx, eax
	mov eax, edx
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov DWORD PTR [ebp+104], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, DWORD PTR [ebp+100]
	xor edx, -1
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+68]
	and ecx, edx
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+76]
	xor edx, ecx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+84]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+76]
	mov DWORD PTR [ebp+120], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, eax
	mov DWORD PTR [ebp+124], ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+72]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+76]
	and ebx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, eax
	xor ebx, DWORD PTR [ebp+100]
	xor ebx, -1
	xor ebx, edx
	and ebx, DWORD PTR [ebp+72]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+132]
	and ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+128], ebx
	mov ebx, DWORD PTR [ebp+68]
	and ebx, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, ebx
	mov DWORD PTR [ebp+140], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+80]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+88]
	xor eax, edx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, eax
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+108]
	xor ebx, DWORD PTR [ebp+116]
	and edx, DWORD PTR [ebp+72]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+84]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, DWORD PTR [ebp+68]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+112]
	xor ebx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+112], edx
	mov edx, DWORD PTR [ebp+68]
	and edx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, edx
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+84]
	xor eax, ebx
	and eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+108]
	mov ebx, DWORD PTR [ebp+144]
	xor ebx, DWORD PTR [ebp+116]
	mov ecx, DWORD PTR [ebp+92]
	xor ecx, DWORD PTR [ebp+104]
	and ecx, DWORD PTR [ebp+72]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+96]
	xor ecx, DWORD PTR [ebp+100]
	xor ecx, -1
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+68]
	and eax, DWORD PTR [ebp+136]
	xor eax, ecx
	mov DWORD PTR [ebp+92], edx
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+140]
	xor eax, edx
	and eax, DWORD PTR [ebp+84]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+112]
	xor eax, DWORD PTR [ebp+100]
	xor eax, -1
	mov edx, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+72]
	xor edx, ecx
	and edx, DWORD PTR [ebp+84]
	xor eax, edx
	and eax, DWORD PTR [ebp+64]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+68]
	xor eax, DWORD PTR [ebp+124]
	mov edx, DWORD PTR [ebp+84]
	and edx, DWORD PTR [ebp+120]
	xor eax, edx
	mov edx, DWORD PTR [ebp+88]
	xor edx, DWORD PTR [ebp+116]
	and edx, DWORD PTR [ebp+72]
	xor edx, DWORD PTR [ebp+120]
	mov ecx, DWORD PTR [ebp+68]
	and ecx, DWORD PTR [ebp+88]
	xor ecx, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+132]
	xor ebx, DWORD PTR [ebp+92]
	and ebx, DWORD PTR [ebp+72]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+84]
	xor edx, ecx
	and edx, DWORD PTR [ebp+64]
	xor eax, edx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 19
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 11
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 29
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 4
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 3
	mov ecx, DWORD PTR [edx]
	shr ecx, 6
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	shr eax, 4
	mov ecx, DWORD PTR [edx]
	shr ecx, 7
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 5
	mov ecx, DWORD PTR [edx]
	shr ecx, 8
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 6
	mov ecx, DWORD PTR [edx]
	shr ecx, 9
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 7
	mov ecx, DWORD PTR [edx]
	shr ecx, 10
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 8
	mov ecx, DWORD PTR [edx]
	shr ecx, 11
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, DWORD PTR [ebp+64]
	mov edx, DWORD PTR [ebp+64]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, edx
	mov DWORD PTR [ebp+92], edx
	mov edx, ecx
	xor edx, ebx
	mov DWORD PTR [ebp+96], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, ebx
	mov DWORD PTR [ebp+104], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+108], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, ebx
	xor edx, ecx
	mov ecx, DWORD PTR [ebp+84]
	xor ecx, eax
	xor ecx, -1
	mov DWORD PTR [ebp+112], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, ecx
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+72]
	and ecx, eax
	mov DWORD PTR [ebp+120], eax
	mov eax, DWORD PTR [ebp+88]
	xor eax, ecx
	mov DWORD PTR [ebp+124], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, DWORD PTR [ebp+104]
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor edx, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, DWORD PTR [ebp+108]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+92]
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+68]
	xor edx, ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+72]
	mov eax, DWORD PTR [ebp+100]
	xor eax, DWORD PTR [ebp+112]
	xor eax, -1
	mov DWORD PTR [ebp+128], edx
	mov edx, eax
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+88]
	xor ecx, edx
	mov DWORD PTR [ebp+136], edx
	mov edx, DWORD PTR [ebp+84]
	xor edx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], eax
	mov eax, edx
	xor eax, DWORD PTR [ebp+124]
	and eax, DWORD PTR [ebp+76]
	xor ecx, eax
	and ecx, DWORD PTR [ebp+80]
	xor ebx, ecx
	mov ecx, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+120]
	mov DWORD PTR [ebp+140], ebx
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+112]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+72]
	xor ebx, ecx
	xor ebx, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+144], ecx
	mov ecx, DWORD PTR [ebp+76]
	and ecx, edx
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+68]
	xor ebx, DWORD PTR [ebp+140]
	xor edx, DWORD PTR [ebp+112]
	xor edx, -1
	mov eax, DWORD PTR [ebp+72]
	and eax, DWORD PTR [ebp+116]
	mov ecx, edx
	xor ecx, eax
	mov DWORD PTR [ebp+116], ebx
	mov ebx, DWORD PTR [ebp+76]
	and ebx, DWORD PTR [ebp+84]
	xor ecx, ebx
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], edx
	mov edx, DWORD PTR [ebp+104]
	xor edx, DWORD PTR [ebp+136]
	and edx, DWORD PTR [ebp+76]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+80]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	and ebx, DWORD PTR [ebp+100]
	and ebx, DWORD PTR [ebp+76]
	xor ebx, DWORD PTR [ebp+88]
	mov edx, DWORD PTR [ebp+80]
	and edx, DWORD PTR [ebp+124]
	xor ebx, edx
	and ebx, DWORD PTR [ebp+68]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+120]
	xor ebx, DWORD PTR [ebp+136]
	xor ebx, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+84]
	mov edx, DWORD PTR [ebp+72]
	and edx, DWORD PTR [ebp+144]
	mov DWORD PTR [ebp+132], ecx
	mov ecx, DWORD PTR [ebp+144]
	xor ecx, edx
	and ecx, DWORD PTR [ebp+76]
	xor eax, ecx
	and eax, DWORD PTR [ebp+80]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+108]
	xor eax, DWORD PTR [ebp+96]
	xor edx, DWORD PTR [ebp+84]
	and edx, DWORD PTR [ebp+76]
	xor eax, edx
	mov edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+80]
	xor eax, edx
	and eax, DWORD PTR [ebp+68]
	xor ebx, eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+116]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+132]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 7
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 22
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 12
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	xor esi, eax
	mov edx, DWORD PTR [ebp+16]
	mov eax, edi
	shr eax, 31
	mov ecx, DWORD PTR [edx]
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+64], eax
	mov eax, edi
	mov ecx, DWORD PTR [edx]
	shr ecx, 1
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+68], eax
	mov eax, edi
	shr eax, 1
	mov ecx, DWORD PTR [edx]
	shr ecx, 2
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+72], eax
	mov eax, edi
	shr eax, 2
	mov ecx, DWORD PTR [edx]
	shr ecx, 3
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+76], eax
	mov eax, edi
	shr eax, 3
	mov ecx, DWORD PTR [edx]
	shr ecx, 4
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+80], eax
	mov eax, edi
	shr eax, 4
	mov ecx, DWORD PTR [edx]
	shr ecx, 5
	xor eax, ecx
	and eax, 1
	mov DWORD PTR [ebp+84], eax
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+64]
	xor ebx, DWORD PTR [ebp+64]
	xor ebx, -1
	mov ecx, DWORD PTR [ebp+64]
	xor ecx, eax
	xor ecx, -1
	mov edx, DWORD PTR [ebp+84]
	xor edx, ecx
	mov DWORD PTR [ebp+88], ebx
	mov ebx, DWORD PTR [ebp+76]
	xor ebx, eax
	xor ebx, -1
	mov DWORD PTR [ebp+92], ecx
	mov ecx, edx
	xor ecx, ebx
	mov DWORD PTR [ebp+96], edx
	mov edx, DWORD PTR [ebp+68]
	xor edx, eax
	xor edx, -1
	xor ecx, edx
	mov DWORD PTR [ebp+100], ecx
	mov ecx, ebx
	and ecx, DWORD PTR [ebp+64]
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+92]
	and eax, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+108], ecx
	mov ecx, ebx
	and ecx, eax
	mov DWORD PTR [ebp+112], ebx
	mov ebx, DWORD PTR [ebp+92]
	xor ebx, ecx
	and ebx, edx
	xor ebx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+116], ecx
	mov ecx, DWORD PTR [ebp+80]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	and ebx, ecx
	xor ebx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	mov DWORD PTR [ebp+120], ecx
	mov ecx, DWORD PTR [ebp+92]
	and ecx, ebx
	mov DWORD PTR [ebp+124], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, ecx
	mov DWORD PTR [ebp+128], ecx
	mov ecx, ebx
	xor ecx, DWORD PTR [ebp+108]
	and ecx, edx
	xor ecx, DWORD PTR [ebp+92]
	mov DWORD PTR [ebp+92], ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, eax
	mov DWORD PTR [ebp+132], eax
	mov eax, DWORD PTR [ebp+112]
	and eax, ebx
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+88]
	xor ebx, eax
	mov DWORD PTR [ebp+88], eax
	mov eax, edx
	and eax, DWORD PTR [ebp+124]
	xor ebx, eax
	and ebx, DWORD PTR [ebp+120]
	xor ecx, ebx
	mov ebx, DWORD PTR [ebp+72]
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	and ecx, ebx
	xor ecx, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+100], ecx
	mov ecx, DWORD PTR [ebp+132]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+140], eax
	mov eax, ecx
	xor eax, DWORD PTR [ebp+88]
	mov DWORD PTR [ebp+144], ecx
	mov ecx, DWORD PTR [ebp+136]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+136], ebx
	mov ebx, DWORD PTR [ebp+112]
	and ebx, ecx
	mov DWORD PTR [ebp+148], ecx
	mov ecx, DWORD PTR [ebp+124]
	xor ecx, ebx
	and ecx, edx
	xor eax, ecx
	mov ecx, DWORD PTR [ebp+116]
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	mov DWORD PTR [ebp+124], ebx
	mov ebx, edx
	and ebx, DWORD PTR [ebp+116]
	xor ebx, ecx
	and ebx, DWORD PTR [ebp+120]
	xor eax, ebx
	mov ebx, DWORD PTR [ebp+84]
	xor ebx, DWORD PTR [ebp+128]
	mov DWORD PTR [ebp+152], ecx
	mov ecx, ebx
	xor ecx, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+108], eax
	mov eax, edx
	and eax, DWORD PTR [ebp+96]
	mov DWORD PTR [ebp+96], edx
	mov edx, ecx
	xor edx, eax
	xor ecx, DWORD PTR [ebp+104]
	xor ecx, -1
	xor ebx, DWORD PTR [ebp+104]
	xor ebx, -1
	and ebx, DWORD PTR [ebp+96]
	xor ecx, ebx
	and ecx, DWORD PTR [ebp+120]
	xor edx, ecx
	and edx, DWORD PTR [ebp+136]
	xor edx, DWORD PTR [ebp+108]
	mov ecx, DWORD PTR [ebp+128]
	xor ecx, DWORD PTR [ebp+116]
	mov ebx, DWORD PTR [ebp+112]
	and ebx, DWORD PTR [ebp+144]
	xor ebx, DWORD PTR [ebp+84]
	mov DWORD PTR [ebp+108], edx
	mov edx, DWORD PTR [ebp+96]
	and edx, ebx
	xor ecx, edx
	mov edx, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+124]
	and edx, DWORD PTR [ebp+120]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+140]
	mov DWORD PTR [ebp+144], eax
	mov eax, DWORD PTR [ebp+132]
	xor eax, DWORD PTR [ebp+116]
	xor eax, DWORD PTR [ebp+140]
	and eax, DWORD PTR [ebp+120]
	xor edx, eax
	and edx, DWORD PTR [ebp+136]
	xor ecx, edx
	mov edx, DWORD PTR [ebp+96]
	and edx, DWORD PTR [ebp+152]
	xor ebx, edx
	mov edx, DWORD PTR [ebp+112]
	and edx, DWORD PTR [ebp+128]
	xor edx, DWORD PTR [ebp+132]
	mov eax, DWORD PTR [ebp+64]
	xor eax, DWORD PTR [ebp+88]
	and eax, DWORD PTR [ebp+96]
	xor eax, edx
	and eax, DWORD PTR [ebp+120]
	xor ebx, eax
	mov eax, DWORD PTR [ebp+92]
	xor eax, DWORD PTR [ebp+144]
	xor edx, DWORD PTR [ebp+104]
	xor edx, -1
	mov DWORD PTR [ebp+104], ecx
	mov ecx, DWORD PTR [ebp+96]
	and ecx, DWORD PTR [ebp+148]
	xor edx, ecx
	and edx, DWORD PTR [ebp+120]
	xor eax, edx
	and eax, DWORD PTR [ebp+136]
	xor ebx, eax
	mov DWORD PTR [ebp+76], ebx
	mov eax, DWORD PTR [ebp+100]
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+108]
	mov DWORD PTR [ebp+68], eax
	mov eax, DWORD PTR [ebp+104]
	mov DWORD PTR [ebp+72], eax
	mov eax, DWORD PTR [ebp+64]
	and eax, 1
	ror eax, 21
	xor esi, eax
	mov eax, DWORD PTR [ebp+68]
	and eax, 1
	ror eax, 15
	xor esi, eax
	mov eax, DWORD PTR [ebp+72]
	and eax, 1
	ror eax, 27
	xor esi, eax
	mov eax, DWORD PTR [ebp+76]
	and eax, 1
	ror eax, 5
	xor esi, eax
	mov eax, esi
	mov esi, edi
	mov edi, eax
	mov eax, DWORD PTR [ebp+16]
	sub eax, 8
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebp+20]
	sub eax, 1
	mov DWORD PTR [ebp+20], eax
	jne 22b
	mov eax, esi
	mov esi, edi
	mov edi, eax
	mov eax, 0
	mov ebx, 0
	mov ecx, edi
	shr ecx, 24
	and ecx, 1
	ror ecx, 1
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 24
	and ecx, 1
	ror ecx, 2
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 16
	and ecx, 1
	ror ecx, 3
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 16
	and ecx, 1
	ror ecx, 4
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 8
	and ecx, 1
	ror ecx, 5
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 8
	and ecx, 1
	ror ecx, 6
	xor ebx, ecx
	mov ecx, edi
	and ecx, 1
	ror ecx, 7
	xor ebx, ecx
	mov ecx, esi
	and ecx, 1
	ror ecx, 8
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 25
	and ecx, 1
	ror ecx, 9
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 25
	and ecx, 1
	ror ecx, 10
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 17
	and ecx, 1
	ror ecx, 11
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 17
	and ecx, 1
	ror ecx, 12
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 9
	and ecx, 1
	ror ecx, 13
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 9
	and ecx, 1
	ror ecx, 14
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 1
	and ecx, 1
	ror ecx, 15
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 1
	and ecx, 1
	ror ecx, 16
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 26
	and ecx, 1
	ror ecx, 17
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 26
	and ecx, 1
	ror ecx, 18
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 18
	and ecx, 1
	ror ecx, 19
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 18
	and ecx, 1
	ror ecx, 20
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 10
	and ecx, 1
	ror ecx, 21
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 10
	and ecx, 1
	ror ecx, 22
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 2
	and ecx, 1
	ror ecx, 23
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 2
	and ecx, 1
	ror ecx, 24
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 27
	and ecx, 1
	ror ecx, 25
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 27
	and ecx, 1
	ror ecx, 26
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 19
	and ecx, 1
	ror ecx, 27
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 19
	and ecx, 1
	ror ecx, 28
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 11
	and ecx, 1
	ror ecx, 29
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 11
	and ecx, 1
	ror ecx, 30
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 3
	and ecx, 1
	ror ecx, 31
	xor ebx, ecx
	mov ecx, esi
	shr ecx, 3
	and ecx, 1
	xor ebx, ecx
	mov ecx, edi
	shr ecx, 28
	and ecx, 1
	ror ecx, 1
	xor eax, ecx
	mov ecx, esi
	shr ecx, 28
	and ecx, 1
	ror ecx, 2
	xor eax, ecx
	mov ecx, edi
	shr ecx, 20
	and ecx, 1
	ror ecx, 3
	xor eax, ecx
	mov ecx, esi
	shr ecx, 20
	and ecx, 1
	ror ecx, 4
	xor eax, ecx
	mov ecx, edi
	shr ecx, 12
	and ecx, 1
	ror ecx, 5
	xor eax, ecx
	mov ecx, esi
	shr ecx, 12
	and ecx, 1
	ror ecx, 6
	xor eax, ecx
	mov ecx, edi
	shr ecx, 4
	and ecx, 1
	ror ecx, 7
	xor eax, ecx
	mov ecx, esi
	shr ecx, 4
	and ecx, 1
	ror ecx, 8
	xor eax, ecx
	mov ecx, edi
	shr ecx, 29
	and ecx, 1
	ror ecx, 9
	xor eax, ecx
	mov ecx, esi
	shr ecx, 29
	and ecx, 1
	ror ecx, 10
	xor eax, ecx
	mov ecx, edi
	shr ecx, 21
	and ecx, 1
	ror ecx, 11
	xor eax, ecx
	mov ecx, esi
	shr ecx, 21
	and ecx, 1
	ror ecx, 12
	xor eax, ecx
	mov ecx, edi
	shr ecx, 13
	and ecx, 1
	ror ecx, 13
	xor eax, ecx
	mov ecx, esi
	shr ecx, 13
	and ecx, 1
	ror ecx, 14
	xor eax, ecx
	mov ecx, edi
	shr ecx, 5
	and ecx, 1
	ror ecx, 15
	xor eax, ecx
	mov ecx, esi
	shr ecx, 5
	and ecx, 1
	ror ecx, 16
	xor eax, ecx
	mov ecx, edi
	shr ecx, 30
	and ecx, 1
	ror ecx, 17
	xor eax, ecx
	mov ecx, esi
	shr ecx, 30
	and ecx, 1
	ror ecx, 18
	xor eax, ecx
	mov ecx, edi
	shr ecx, 22
	and ecx, 1
	ror ecx, 19
	xor eax, ecx
	mov ecx, esi
	shr ecx, 22
	and ecx, 1
	ror ecx, 20
	xor eax, ecx
	mov ecx, edi
	shr ecx, 14
	and ecx, 1
	ror ecx, 21
	xor eax, ecx
	mov ecx, esi
	shr ecx, 14
	and ecx, 1
	ror ecx, 22
	xor eax, ecx
	mov ecx, edi
	shr ecx, 6
	and ecx, 1
	ror ecx, 23
	xor eax, ecx
	mov ecx, esi
	shr ecx, 6
	and ecx, 1
	ror ecx, 24
	xor eax, ecx
	mov ecx, edi
	shr ecx, 31
	and ecx, 1
	ror ecx, 25
	xor eax, ecx
	mov ecx, esi
	shr ecx, 31
	and ecx, 1
	ror ecx, 26
	xor eax, ecx
	mov ecx, edi
	shr ecx, 23
	and ecx, 1
	ror ecx, 27
	xor eax, ecx
	mov ecx, esi
	shr ecx, 23
	and ecx, 1
	ror ecx, 28
	xor eax, ecx
	mov ecx, edi
	shr ecx, 15
	and ecx, 1
	ror ecx, 29
	xor eax, ecx
	mov ecx, esi
	shr ecx, 15
	and ecx, 1
	ror ecx, 30
	xor eax, ecx
	mov ecx, edi
	shr ecx, 7
	and ecx, 1
	ror ecx, 31
	xor eax, ecx
	mov ecx, esi
	shr ecx, 7
	and ecx, 1
	xor eax, ecx
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+28], ebx
	mov eax, ebp
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	mov edx, eax
	mov ecx, DWORD PTR [edx+28]
	mov eax, DWORD PTR [edx+24]
	bswap ecx
	bswap eax
	mov edx, DWORD PTR [esp+8]
	mov DWORD PTR [edx], ecx
	mov DWORD PTR [edx+4], eax
	ret
	.p2align 6
