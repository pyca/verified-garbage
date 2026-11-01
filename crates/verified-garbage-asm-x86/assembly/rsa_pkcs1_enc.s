// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-1072]
	mov edi, esp
	add edi, 48
	mov esi, DWORD PTR [esp+1124]
	mov ecx, DWORD PTR [esp+1128]
	mov eax, 0
	mov BYTE PTR [edi], al
	mov eax, 2
	mov BYTE PTR [edi+1], al
	add edi, 2
	mov ebx, 0
20:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	sub eax, 1
	sbb eax, eax
	or ebx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 20b
	mov eax, 0
	mov BYTE PTR [edi], al
	add edi, 1
	mov DWORD PTR [esp+40], ebx
	mov ebx, edi
	mov esi, DWORD PTR [esp+1116]
	mov ecx, DWORD PTR [esp+1120]
	cmp ecx, 0
	je 21f
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [esp+1092]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1140]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1144]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1112]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 48
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+1132]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+1136]
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	mov ebx, DWORD PTR [esp+40]
	xor ebx, -1
	mov edi, eax
	and edi, ebx
	mov esi, DWORD PTR [esp+1092]
	mov ecx, DWORD PTR [esp+1104]
24:
	movzx edx, BYTE PTR [esi]
	and edx, ebx
	mov BYTE PTR [esi], dl
	add esi, 1
	sub ecx, 1
	jne 24b
	mov esi, esp
	add esi, 48
	mov ecx, DWORD PTR [esp+1104]
	mov eax, 0
25:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 25b
	mov eax, edi
	lea esp, [esp+1072]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-104]
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov DWORD PTR [esp+80], eax
	mov esi, DWORD PTR [esp+208]
	add esi, 1552
	mov ecx, DWORD PTR [esp+140]
	mov eax, 0
20:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 20b
	mov ebx, DWORD PTR [esp+208]
	add ebx, 1552
	add ebx, DWORD PTR [esp+140]
	sub ebx, DWORD PTR [esp+156]
	mov esi, DWORD PTR [esp+152]
	mov ecx, DWORD PTR [esp+156]
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	push edi
	call {vg_sha256_init}
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 1552
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov eax, DWORD PTR [esp+140]
	mov ecx, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+160]
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, DWORD PTR [esp+140]
	add eax, 64
	mov ecx, 0
	mov edi, DWORD PTR [esp+208]
	add edi, 240
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 8
	mov DWORD PTR [esp+88], eax
22:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 108
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 110
	mov BYTE PTR [ebx+4], al
	mov eax, 103
	mov BYTE PTR [ebx+5], al
	mov eax, 116
	mov BYTE PTR [ebx+6], al
	mov eax, 104
	mov BYTE PTR [ebx+7], al
	mov eax, 8
	mov BYTE PTR [ebx+8], al
	mov eax, 0
	mov BYTE PTR [ebx+9], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 10
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 74
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 272
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 22b
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+140]
	add eax, 31
	shr eax, 5
	mov DWORD PTR [esp+88], eax
23:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 109
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 115
	mov BYTE PTR [ebx+4], al
	mov eax, 115
	mov BYTE PTR [ebx+5], al
	mov eax, 97
	mov BYTE PTR [ebx+6], al
	mov eax, 103
	mov BYTE PTR [ebx+7], al
	mov eax, 101
	mov BYTE PTR [ebx+8], al
	mov eax, edx
	shr eax, 5
	mov BYTE PTR [ebx+9], al
	mov eax, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov BYTE PTR [ebx+10], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 11
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 75
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 528
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 23b
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 11
	mov eax, 0
24:
	add eax, eax
	add eax, 1
	cmp eax, ecx
	jb 24b
	mov esi, DWORD PTR [esp+208]
	add esi, 272
	mov edi, eax
	mov ebp, ecx
	mov ebx, 0
	mov ecx, 128
25:
	movzx eax, BYTE PTR [esi]
	ror eax, 24
	movzx edx, BYTE PTR [esi+1]
	or eax, edx
	and eax, edi
	mov edx, ebp
	sub edx, eax
	sbb edx, edx
	xor edx, -1
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	add esi, 2
	sub ecx, 1
	jne 25b
	mov DWORD PTR [esp+92], ebx
	mov esi, DWORD PTR [esp+124]
	add esi, 2
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 2
	mov edx, 2
	mov ebx, 0
	mov edi, 0
26:
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	mov ebp, ebx
	xor ebp, -1
	and ebp, eax
	and ebp, edx
	or edi, ebp
	or ebx, eax
	add edx, 1
	add esi, 1
	sub ecx, 1
	jne 26b
	mov esi, DWORD PTR [esp+124]
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	movzx edx, BYTE PTR [esi+1]
	xor edx, 2
	sub edx, 1
	sbb edx, edx
	and eax, edx
	and eax, ebx
	mov edx, edi
	sub edx, 10
	sbb edx, edx
	xor edx, -1
	and eax, edx
	mov DWORD PTR [esp+96], eax
	mov edx, DWORD PTR [esp+140]
	sub edx, edi
	sub edx, 1
	mov ecx, DWORD PTR [esp+92]
	xor edx, ecx
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [esp+80]
	xor eax, 1
	sub eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov ebx, DWORD PTR [esp+140]
	sub ebx, edx
	and edx, eax
	mov esi, DWORD PTR [esp+132]
	mov DWORD PTR [esi], edx
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov esi, DWORD PTR [esp+124]
	mov edi, DWORD PTR [esp+208]
	add edi, 528
	mov edx, 0
	mov ecx, DWORD PTR [esp+140]
27:
	movzx eax, BYTE PTR [esi]
	movzx ebp, BYTE PTR [edi]
	xor eax, ebp
	and eax, DWORD PTR [esp+96]
	xor eax, ebp
	mov ebp, edx
	sub ebp, ebx
	sbb ebp, ebp
	xor ebp, -1
	and ebp, DWORD PTR [esp+100]
	and eax, ebp
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 27b
	mov eax, DWORD PTR [esp+80]
	lea esp, [esp+104]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_sha256_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-104]
	mov eax, DWORD PTR [esp+124]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+136]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+144]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+148]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+160]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+140]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+168]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+172]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+68], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+212]
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov DWORD PTR [esp+80], eax
	mov esi, DWORD PTR [esp+208]
	add esi, 1552
	mov ecx, DWORD PTR [esp+140]
	mov eax, 0
20:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 20b
	mov ebx, DWORD PTR [esp+208]
	add ebx, 1552
	add ebx, DWORD PTR [esp+140]
	sub ebx, DWORD PTR [esp+156]
	mov esi, DWORD PTR [esp+152]
	mov ecx, DWORD PTR [esp+156]
21:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 21b
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	push edi
	call {vg_sha256_init}
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 1552
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov eax, DWORD PTR [esp+140]
	mov ecx, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edx
	push ecx
	push eax
	push edi
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 208
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+160]
	mov ecx, DWORD PTR [esp+140]
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, DWORD PTR [esp+140]
	add eax, 64
	mov ecx, 0
	mov edi, DWORD PTR [esp+208]
	add edi, 240
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, 8
	mov DWORD PTR [esp+88], eax
22:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 108
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 110
	mov BYTE PTR [ebx+4], al
	mov eax, 103
	mov BYTE PTR [ebx+5], al
	mov eax, 116
	mov BYTE PTR [ebx+6], al
	mov eax, 104
	mov BYTE PTR [ebx+7], al
	mov eax, 8
	mov BYTE PTR [ebx+8], al
	mov eax, 0
	mov BYTE PTR [ebx+9], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 10
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 74
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 272
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 22b
	mov eax, 0
	mov DWORD PTR [esp+84], eax
	mov eax, DWORD PTR [esp+140]
	add eax, 31
	shr eax, 5
	mov DWORD PTR [esp+88], eax
23:
	mov ebx, DWORD PTR [esp+208]
	add ebx, 192
	mov ecx, DWORD PTR [esp+84]
	mov edx, DWORD PTR [esp+140]
	mov eax, 0
	mov BYTE PTR [ebx], al
	mov BYTE PTR [ebx+1], cl
	mov eax, 109
	mov BYTE PTR [ebx+2], al
	mov eax, 101
	mov BYTE PTR [ebx+3], al
	mov eax, 115
	mov BYTE PTR [ebx+4], al
	mov eax, 115
	mov BYTE PTR [ebx+5], al
	mov eax, 97
	mov BYTE PTR [ebx+6], al
	mov eax, 103
	mov BYTE PTR [ebx+7], al
	mov eax, 101
	mov BYTE PTR [ebx+8], al
	mov eax, edx
	shr eax, 5
	mov BYTE PTR [ebx+9], al
	mov eax, edx
	add eax, eax
	add eax, eax
	add eax, eax
	mov BYTE PTR [ebx+10], al
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov edx, DWORD PTR [esp+208]
	add edx, 240
	mov ecx, 32
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push esi
	push edi
	call {vg_hmac_sha256_init_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+208]
	add edi, 0
	mov esi, 64
	mov eax, 0
	mov edx, DWORD PTR [esp+208]
	add edx, 192
	mov ecx, 11
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push ecx
	push edx
	push eax
	push esi
	push edi
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+208]
	add edx, 0
	mov esi, DWORD PTR [esp+208]
	add esi, 96
	mov eax, 75
	mov ecx, 0
	mov edi, DWORD PTR [esp+84]
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, edi
	add edi, DWORD PTR [esp+208]
	add edi, 528
	mov ebp, DWORD PTR [esp+208]
	add ebp, 2576
	push ebp
	push edi
	push ecx
	push eax
	push esi
	push edx
	call {vg_hmac_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+84]
	add eax, 1
	mov DWORD PTR [esp+84], eax
	cmp eax, DWORD PTR [esp+88]
	jne 23b
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 11
	mov eax, 0
24:
	add eax, eax
	add eax, 1
	cmp eax, ecx
	jb 24b
	mov esi, DWORD PTR [esp+208]
	add esi, 272
	mov edi, eax
	mov ebp, ecx
	mov ebx, 0
	mov ecx, 128
25:
	movzx eax, BYTE PTR [esi]
	ror eax, 24
	movzx edx, BYTE PTR [esi+1]
	or eax, edx
	and eax, edi
	mov edx, ebp
	sub edx, eax
	sbb edx, edx
	xor edx, -1
	xor eax, ebx
	and eax, edx
	xor ebx, eax
	add esi, 2
	sub ecx, 1
	jne 25b
	mov DWORD PTR [esp+92], ebx
	mov esi, DWORD PTR [esp+124]
	add esi, 2
	mov ecx, DWORD PTR [esp+140]
	sub ecx, 2
	mov edx, 2
	mov ebx, 0
	mov edi, 0
26:
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	mov ebp, ebx
	xor ebp, -1
	and ebp, eax
	and ebp, edx
	or edi, ebp
	or ebx, eax
	add edx, 1
	add esi, 1
	sub ecx, 1
	jne 26b
	mov esi, DWORD PTR [esp+124]
	movzx eax, BYTE PTR [esi]
	sub eax, 1
	sbb eax, eax
	movzx edx, BYTE PTR [esi+1]
	xor edx, 2
	sub edx, 1
	sbb edx, edx
	and eax, edx
	and eax, ebx
	mov edx, edi
	sub edx, 10
	sbb edx, edx
	xor edx, -1
	and eax, edx
	mov DWORD PTR [esp+96], eax
	mov edx, DWORD PTR [esp+140]
	sub edx, edi
	sub edx, 1
	mov ecx, DWORD PTR [esp+92]
	xor edx, ecx
	and edx, eax
	xor edx, ecx
	mov eax, DWORD PTR [esp+80]
	xor eax, 1
	sub eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov ebx, DWORD PTR [esp+140]
	sub ebx, edx
	and edx, eax
	mov esi, DWORD PTR [esp+132]
	mov DWORD PTR [esi], edx
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov esi, DWORD PTR [esp+124]
	mov edi, DWORD PTR [esp+208]
	add edi, 528
	mov edx, 0
	mov ecx, DWORD PTR [esp+140]
27:
	movzx eax, BYTE PTR [esi]
	movzx ebp, BYTE PTR [edi]
	xor eax, ebp
	and eax, DWORD PTR [esp+96]
	xor eax, ebp
	mov ebp, edx
	sub ebp, ebx
	sbb ebp, ebp
	xor ebp, -1
	and ebp, DWORD PTR [esp+100]
	and eax, ebp
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 27b
	mov eax, DWORD PTR [esp+80]
	lea esp, [esp+104]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
