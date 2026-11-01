// The functions of `src/internal/vg_aes_xts_decrypt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_decrypt:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+24]
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
22:
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov edi, DWORD PTR [ebx+12]
	add eax, eax
	adc ecx, ecx
	adc edx, edx
	adc edi, edi
	sbb ebp, ebp
	and ebp, 135
	xor eax, ebp
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], edi
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 22b
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+24]
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebp+2048]
	xor eax, ecx
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [ebp+2052]
	xor eax, ecx
	mov DWORD PTR [ebx+4], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [ebp+2056]
	xor eax, ecx
	mov DWORD PTR [ebx+8], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [ebp+2060]
	xor eax, ecx
	mov DWORD PTR [ebx+12], eax
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, esi
	mov ebx, DWORD PTR [esp+20]
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_decrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
23:
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [ebx]
	xor eax, ecx
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	mov ecx, DWORD PTR [ebx+4]
	xor eax, ecx
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	mov ecx, DWORD PTR [ebx+8]
	xor eax, ecx
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	mov ecx, DWORD PTR [ebx+12]
	xor eax, ecx
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov edi, DWORD PTR [ebx+12]
	add eax, eax
	adc ecx, ecx
	adc edx, edx
	adc edi, edi
	sbb ebp, ebp
	and ebp, 135
	xor eax, ebp
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], edi
	add esi, 16
	mov eax, DWORD PTR [esp+20]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, DWORD PTR [esp+16]
	cmp esi, eax
	jne 23b
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
