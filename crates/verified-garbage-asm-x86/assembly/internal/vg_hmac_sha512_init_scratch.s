// The functions of `src/internal/vg_hmac_sha512_init_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_init_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+272], ebx
	mov DWORD PTR [eax+276], esi
	mov DWORD PTR [eax+280], edi
	mov DWORD PTR [eax+284], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_sha512_init}
	pop eax
	push esi
	call {vg_sha512_init}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov DWORD PTR [ebx+80], ecx
	mov DWORD PTR [ebx+84], ecx
	mov DWORD PTR [ebx+88], ecx
	mov DWORD PTR [ebx+92], ecx
	mov DWORD PTR [ebx+96], ecx
	mov DWORD PTR [ebx+100], ecx
	mov DWORD PTR [ebx+104], ecx
	mov DWORD PTR [ebx+108], ecx
	mov DWORD PTR [ebx+112], ecx
	mov DWORD PTR [ebx+116], ecx
	mov DWORD PTR [ebx+120], ecx
	mov DWORD PTR [ebx+124], ecx
	mov DWORD PTR [ebx+128], ecx
	mov DWORD PTR [ebx+132], ecx
	mov DWORD PTR [ebx+136], ecx
	mov DWORD PTR [ebx+140], ecx
	mov DWORD PTR [ebx+144], ecx
	mov DWORD PTR [ebx+148], ecx
	mov DWORD PTR [ebx+152], ecx
	mov DWORD PTR [ebx+156], ecx
	mov DWORD PTR [ebx+160], ecx
	mov DWORD PTR [ebx+164], ecx
	mov DWORD PTR [ebx+168], ecx
	mov DWORD PTR [ebx+172], ecx
	mov DWORD PTR [ebx+176], ecx
	mov DWORD PTR [ebx+180], ecx
	mov DWORD PTR [ebx+184], ecx
	mov DWORD PTR [ebx+188], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 64
	test ecx, ecx
	je 20f
22:
	movzx eax, BYTE PTR [edi]
	xor eax, 54
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebx+64]
	xor eax, 1785358954
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [ebx+68]
	xor eax, 1785358954
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [ebx+72]
	xor eax, 1785358954
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [ebx+76]
	xor eax, 1785358954
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [ebx+80]
	xor eax, 1785358954
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [ebx+84]
	xor eax, 1785358954
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [ebx+88]
	xor eax, 1785358954
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [ebx+92]
	xor eax, 1785358954
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [ebx+96]
	xor eax, 1785358954
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [ebx+100]
	xor eax, 1785358954
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [ebx+104]
	xor eax, 1785358954
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [ebx+108]
	xor eax, 1785358954
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [ebx+112]
	xor eax, 1785358954
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [ebx+116]
	xor eax, 1785358954
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [ebx+120]
	xor eax, 1785358954
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [ebx+124]
	xor eax, 1785358954
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [ebx+128]
	xor eax, 1785358954
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [ebx+132]
	xor eax, 1785358954
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [ebx+136]
	xor eax, 1785358954
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [ebx+140]
	xor eax, 1785358954
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [ebx+144]
	xor eax, 1785358954
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [ebx+148]
	xor eax, 1785358954
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [ebx+152]
	xor eax, 1785358954
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [ebx+156]
	xor eax, 1785358954
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [ebx+160]
	xor eax, 1785358954
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [ebx+164]
	xor eax, 1785358954
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [ebx+168]
	xor eax, 1785358954
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [ebx+172]
	xor eax, 1785358954
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [ebx+176]
	xor eax, 1785358954
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [ebx+180]
	xor eax, 1785358954
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [ebx+184]
	xor eax, 1785358954
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [ebx+188]
	xor eax, 1785358954
	mov DWORD PTR [esi+188], eax
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 64
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha512_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+272]
	mov esi, DWORD PTR [eax+276]
	mov edi, DWORD PTR [eax+280]
	mov ebp, DWORD PTR [eax+284]
	ret
	.p2align 6
