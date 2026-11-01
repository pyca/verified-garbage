// The functions of `src/internal/vg_pbkdf2_hmac_sha1_iterate.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_iterate:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+160], ebx
	mov DWORD PTR [eax+164], esi
	mov DWORD PTR [eax+168], edi
	mov DWORD PTR [eax+172], ebp
	mov ebp, eax
	mov esi, DWORD PTR [esp+4]
	mov edi, DWORD PTR [esp+12]
	mov ebx, ebp
	add ebx, 176
	mov edx, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [edx]
	mov DWORD PTR [ebx+20], ecx
	mov ecx, DWORD PTR [edx+4]
	mov DWORD PTR [ebx+24], ecx
	mov ecx, DWORD PTR [edx+8]
	mov DWORD PTR [ebx+28], ecx
	mov ecx, DWORD PTR [edx+12]
	mov DWORD PTR [ebx+32], ecx
	mov ecx, DWORD PTR [edx+16]
	mov DWORD PTR [ebx+36], ecx
	mov ecx, 128
	mov DWORD PTR [ebx+40], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+44], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+48], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+52], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+56], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+60], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+72], ecx
	mov ecx, 0
	mov DWORD PTR [ebx+76], ecx
	mov ecx, -1610481664
	mov DWORD PTR [ebx+80], ecx
	test edi, edi
	je 20f
22:
	mov ecx, DWORD PTR [esi]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+4]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+8]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+12]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+16]
	mov DWORD PTR [ebx+16], ecx
	mov eax, ebx
	add eax, 20
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha1_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 20
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov ecx, DWORD PTR [esi+84]
	mov DWORD PTR [ebx], ecx
	mov ecx, DWORD PTR [esi+88]
	mov DWORD PTR [ebx+4], ecx
	mov ecx, DWORD PTR [esi+92]
	mov DWORD PTR [ebx+8], ecx
	mov ecx, DWORD PTR [esi+96]
	mov DWORD PTR [ebx+12], ecx
	mov ecx, DWORD PTR [esi+100]
	mov DWORD PTR [ebx+16], ecx
	mov eax, ebx
	add eax, 20
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha1_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebx
	add eax, 20
	mov ecx, DWORD PTR [ebx]
	bswap ecx
	mov DWORD PTR [eax], ecx
	mov ecx, DWORD PTR [ebx+4]
	bswap ecx
	mov DWORD PTR [eax+4], ecx
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	mov DWORD PTR [eax+8], ecx
	mov ecx, DWORD PTR [ebx+12]
	bswap ecx
	mov DWORD PTR [eax+12], ecx
	mov ecx, DWORD PTR [ebx+16]
	bswap ecx
	mov DWORD PTR [eax+16], ecx
	mov edx, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [ebx+20]
	xor ecx, DWORD PTR [edx]
	mov DWORD PTR [edx], ecx
	mov ecx, DWORD PTR [ebx+24]
	xor ecx, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], ecx
	mov ecx, DWORD PTR [ebx+28]
	xor ecx, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], ecx
	mov ecx, DWORD PTR [ebx+32]
	xor ecx, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], ecx
	mov ecx, DWORD PTR [ebx+36]
	xor ecx, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], ecx
	sub edi, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, ebp
	mov ebx, DWORD PTR [eax+160]
	mov esi, DWORD PTR [eax+164]
	mov edi, DWORD PTR [eax+168]
	mov ebp, DWORD PTR [eax+172]
	ret
	.p2align 6
