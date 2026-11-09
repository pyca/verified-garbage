// The functions of `src/aes_ctr.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
22:
	mov ebp, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov eax, DWORD PTR [ebp+2048]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebp+2052]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebp+2056]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebp+2060]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, ebp
	add ebx, 2048
	mov edi, 1
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+24]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebp+2048]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebp+2052]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebp+2056]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebp+2060]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	add eax, 1
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	adc ecx, 0
	mov edx, DWORD PTR [ebx+4]
	bswap edx
	adc edx, 0
	mov edi, DWORD PTR [ebx]
	bswap edi
	adc edi, 0
	bswap eax
	mov DWORD PTR [ebx+12], eax
	bswap ecx
	mov DWORD PTR [ebx+8], ecx
	bswap edx
	mov DWORD PTR [ebx+4], edx
	bswap edi
	mov DWORD PTR [ebx], edi
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6

vg_aes_ctr_final_aesni:
	lea esp, [esp-64]
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+28]
	mov ecx, 0
	mov DWORD PTR [eax+16], ecx
	mov DWORD PTR [eax+20], ecx
	mov DWORD PTR [eax+24], ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, eax
	add ebx, 16
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov esi, 1
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+28]
	add ebx, 16
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	mov ecx, 0
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	lea esp, [esp+64]
	ret
	.p2align 6

vg_aes_ctr:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
22:
	mov ebp, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov eax, DWORD PTR [ebp+2048]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebp+2052]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebp+2056]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebp+2060]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, ebp
	add ebx, 2048
	mov edi, 1
	push ebp
	push edi
	push ebx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+24]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebp+2048]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebp+2052]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebp+2056]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebp+2060]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	add eax, 1
	mov ecx, DWORD PTR [ebx+8]
	bswap ecx
	adc ecx, 0
	mov edx, DWORD PTR [ebx+4]
	bswap edx
	adc edx, 0
	mov edi, DWORD PTR [ebx]
	bswap edi
	adc edi, 0
	bswap eax
	mov DWORD PTR [ebx+12], eax
	bswap ecx
	mov DWORD PTR [ebx+8], ecx
	bswap edx
	mov DWORD PTR [ebx+4], edx
	bswap edi
	mov DWORD PTR [ebx], edi
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6

vg_aes_ctr_final:
	lea esp, [esp-64]
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+80]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	mov esi, DWORD PTR [esp+20]
	shr esi, 4
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+20]
	and eax, 15
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+28]
	mov ecx, 0
	mov DWORD PTR [eax+16], ecx
	mov DWORD PTR [eax+20], ecx
	mov DWORD PTR [eax+24], ecx
	mov DWORD PTR [eax+28], ecx
	mov ebx, eax
	add ebx, 16
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov esi, 1
	mov edi, DWORD PTR [esp+24]
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [esp+28]
	add ebx, 16
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov eax, ebp
	and ebp, 15
	sub eax, ebp
	add esi, eax
22:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax]
	mov esi, DWORD PTR [eax+4]
	mov edi, DWORD PTR [eax+8]
	mov ebp, DWORD PTR [eax+12]
	mov ecx, 0
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	lea esp, [esp+64]
	ret
	.p2align 6
