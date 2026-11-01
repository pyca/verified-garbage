// The functions of `src/internal/vg_hmac_sha224_init_scratch.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_init_scratch:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+160], ebx
	mov DWORD PTR [eax+164], esi
	mov DWORD PTR [eax+168], edi
	mov DWORD PTR [eax+172], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	push ebx
	call {vg_sha224_init}
	pop eax
	push esi
	call {vg_sha224_init}
	pop eax
	mov ecx, 909522486
	mov DWORD PTR [ebx+32], ecx
	mov DWORD PTR [ebx+36], ecx
	mov DWORD PTR [ebx+40], ecx
	mov DWORD PTR [ebx+44], ecx
	mov DWORD PTR [ebx+48], ecx
	mov DWORD PTR [ebx+52], ecx
	mov DWORD PTR [ebx+56], ecx
	mov DWORD PTR [ebx+60], ecx
	mov DWORD PTR [ebx+64], ecx
	mov DWORD PTR [ebx+68], ecx
	mov DWORD PTR [ebx+72], ecx
	mov DWORD PTR [ebx+76], ecx
	mov DWORD PTR [ebx+80], ecx
	mov DWORD PTR [ebx+84], ecx
	mov DWORD PTR [ebx+88], ecx
	mov DWORD PTR [ebx+92], ecx
	mov edi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	mov edx, ebx
	add edx, 32
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
	mov eax, DWORD PTR [ebx+32]
	xor eax, 1785358954
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [ebx+36]
	xor eax, 1785358954
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [ebx+40]
	xor eax, 1785358954
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [ebx+44]
	xor eax, 1785358954
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [ebx+48]
	xor eax, 1785358954
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [ebx+52]
	xor eax, 1785358954
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [ebx+56]
	xor eax, 1785358954
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [ebx+60]
	xor eax, 1785358954
	mov DWORD PTR [esi+60], eax
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
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, esi
	mov eax, ebx
	add eax, 32
	mov ecx, 1
	push ebp
	push ecx
	push eax
	push ebx
	call {vg_sha256_compress}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	mov ebx, DWORD PTR [eax+160]
	mov esi, DWORD PTR [eax+164]
	mov edi, DWORD PTR [eax+168]
	mov ebp, DWORD PTR [eax+172]
	ret
	.p2align 6
