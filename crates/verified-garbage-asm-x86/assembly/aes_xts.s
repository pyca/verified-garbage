// The functions of `src/aes_xts.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_unit_aesni:
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+2208], ebx
	mov DWORD PTR [eax+2212], esi
	mov DWORD PTR [eax+2216], edi
	mov DWORD PTR [eax+2220], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [ecx]
	mov DWORD PTR [ebp+2176], edx
	mov edx, DWORD PTR [ecx+4]
	mov DWORD PTR [ebp+2180], edx
	mov edx, DWORD PTR [ecx+8]
	mov DWORD PTR [ebp+2184], edx
	mov edx, DWORD PTR [ecx+12]
	mov DWORD PTR [ebp+2188], edx
	mov eax, 0
	mov DWORD PTR [ebp+2192], eax
	mov DWORD PTR [ebp+2196], eax
	mov DWORD PTR [ebp+2200], eax
	mov DWORD PTR [ebp+2204], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2192
	mov ebx, ebp
	add ebx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov ebx, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	shr edi, 4
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+24]
	and esi, 15
	je 20f
	mov edx, DWORD PTR [esp+24]
	sub edx, esi
	mov ecx, DWORD PTR [esp+20]
	add edx, ecx
	sub edx, 16
	mov ecx, esi
22:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edx+16]
	mov BYTE PTR [edx], bl
	mov BYTE PTR [edx+16], al
	add edx, 1
	sub ecx, 1
	jne 22b
	mov ebx, DWORD PTR [esp+24]
	sub ebx, esi
	add ebx, DWORD PTR [esp+20]
	sub ebx, 16
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+2208]
	mov esi, DWORD PTR [eax+2212]
	mov edi, DWORD PTR [eax+2216]
	mov ebp, DWORD PTR [eax+2220]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_aesni:
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+2208], ebx
	mov DWORD PTR [eax+2212], esi
	mov DWORD PTR [eax+2216], edi
	mov DWORD PTR [eax+2220], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [ecx]
	mov DWORD PTR [ebp+2176], edx
	mov edx, DWORD PTR [ecx+4]
	mov DWORD PTR [ebp+2180], edx
	mov edx, DWORD PTR [ecx+8]
	mov DWORD PTR [ebp+2184], edx
	mov edx, DWORD PTR [ecx+12]
	mov DWORD PTR [ebp+2188], edx
	mov eax, 0
	mov DWORD PTR [ebp+2192], eax
	mov DWORD PTR [ebp+2196], eax
	mov DWORD PTR [ebp+2200], eax
	mov DWORD PTR [ebp+2204], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2192
	mov ebx, ebp
	add ebx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+24]
	and esi, 15
	je 20f
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov ebx, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	shr edi, 4
	sub edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [ebp+2176]
	mov DWORD PTR [ebp+2192], eax
	mov eax, DWORD PTR [ebp+2180]
	mov DWORD PTR [ebp+2196], eax
	mov eax, DWORD PTR [ebp+2184]
	mov DWORD PTR [ebp+2200], eax
	mov eax, DWORD PTR [ebp+2188]
	mov DWORD PTR [ebp+2204], eax
	mov ebx, ebp
	add ebx, 2192
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
	mov ebx, DWORD PTR [esp+24]
	sub ebx, esi
	add ebx, DWORD PTR [esp+20]
	sub ebx, 16
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2192
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+24]
	sub edx, esi
	mov ecx, DWORD PTR [esp+20]
	add edx, ecx
	sub edx, 16
	mov ecx, esi
22:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edx+16]
	mov BYTE PTR [edx], bl
	mov BYTE PTR [edx+16], al
	add edx, 1
	sub ecx, 1
	jne 22b
	mov ebx, DWORD PTR [esp+24]
	sub ebx, esi
	add ebx, DWORD PTR [esp+20]
	sub ebx, 16
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov ebx, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	shr edi, 4
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+2208]
	mov esi, DWORD PTR [eax+2212]
	mov edi, DWORD PTR [eax+2216]
	mov ebp, DWORD PTR [eax+2220]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit:
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+2208], ebx
	mov DWORD PTR [eax+2212], esi
	mov DWORD PTR [eax+2216], edi
	mov DWORD PTR [eax+2220], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [ecx]
	mov DWORD PTR [ebp+2176], edx
	mov edx, DWORD PTR [ecx+4]
	mov DWORD PTR [ebp+2180], edx
	mov edx, DWORD PTR [ecx+8]
	mov DWORD PTR [ebp+2184], edx
	mov edx, DWORD PTR [ecx+12]
	mov DWORD PTR [ebp+2188], edx
	mov eax, 0
	mov DWORD PTR [ebp+2192], eax
	mov DWORD PTR [ebp+2196], eax
	mov DWORD PTR [ebp+2200], eax
	mov DWORD PTR [ebp+2204], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2192
	mov ebx, ebp
	add ebx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov ebx, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	shr edi, 4
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+24]
	and esi, 15
	je 20f
	mov edx, DWORD PTR [esp+24]
	sub edx, esi
	mov ecx, DWORD PTR [esp+20]
	add edx, ecx
	sub edx, 16
	mov ecx, esi
22:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edx+16]
	mov BYTE PTR [edx], bl
	mov BYTE PTR [edx+16], al
	add edx, 1
	sub ecx, 1
	jne 22b
	mov ebx, DWORD PTR [esp+24]
	sub ebx, esi
	add ebx, DWORD PTR [esp+20]
	sub ebx, 16
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+2208]
	mov esi, DWORD PTR [eax+2212]
	mov edi, DWORD PTR [eax+2216]
	mov ebp, DWORD PTR [eax+2220]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit:
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+2208], ebx
	mov DWORD PTR [eax+2212], esi
	mov DWORD PTR [eax+2216], edi
	mov DWORD PTR [eax+2220], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [ecx]
	mov DWORD PTR [ebp+2176], edx
	mov edx, DWORD PTR [ecx+4]
	mov DWORD PTR [ebp+2180], edx
	mov edx, DWORD PTR [ecx+8]
	mov DWORD PTR [ebp+2184], edx
	mov edx, DWORD PTR [ecx+12]
	mov DWORD PTR [ebp+2188], edx
	mov eax, 0
	mov DWORD PTR [ebp+2192], eax
	mov DWORD PTR [ebp+2196], eax
	mov DWORD PTR [ebp+2200], eax
	mov DWORD PTR [ebp+2204], eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2192
	mov ebx, ebp
	add ebx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_encrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, DWORD PTR [esp+24]
	and esi, 15
	je 20f
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov ebx, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	shr edi, 4
	sub edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [ebp+2176]
	mov DWORD PTR [ebp+2192], eax
	mov eax, DWORD PTR [ebp+2180]
	mov DWORD PTR [ebp+2196], eax
	mov eax, DWORD PTR [ebp+2184]
	mov DWORD PTR [ebp+2200], eax
	mov eax, DWORD PTR [ebp+2188]
	mov DWORD PTR [ebp+2204], eax
	mov ebx, ebp
	add ebx, 2192
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
	mov ebx, DWORD PTR [esp+24]
	sub ebx, esi
	add ebx, DWORD PTR [esp+20]
	sub ebx, 16
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2192
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+24]
	sub edx, esi
	mov ecx, DWORD PTR [esp+20]
	add edx, ecx
	sub edx, 16
	mov ecx, esi
22:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edx+16]
	mov BYTE PTR [edx], bl
	mov BYTE PTR [edx+16], al
	add edx, 1
	sub ecx, 1
	jne 22b
	mov ebx, DWORD PTR [esp+24]
	sub ebx, esi
	add ebx, DWORD PTR [esp+20]
	sub ebx, 16
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov edi, 1
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 21f
20:
	mov ebp, DWORD PTR [esp+28]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	mov edx, ebp
	add edx, 2176
	mov ebx, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+24]
	shr edi, 4
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_xts_decrypt}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+2208]
	mov esi, DWORD PTR [eax+2212]
	mov edi, DWORD PTR [eax+2216]
	mov ebp, DWORD PTR [eax+2220]
	ret
	.p2align 6
