// The functions of `src/rsa_oaep_sha224_mgf1_sha1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esp+176]
	sub eax, 58
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 20f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 28
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1053
	mov ecx, 28
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 25f
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	jmp 26f
25:
26:
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
28:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
29:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 28b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
210:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
211:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 210b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+212]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha1_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esp+176]
	sub eax, 58
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 20f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 28
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1053
	mov ecx, 28
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 25f
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	jmp 26f
25:
26:
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
28:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
29:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 28b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
210:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
211:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 210b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+212]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha256_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esp+176]
	sub eax, 58
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 20f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 28
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1053
	mov ecx, 28
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 25f
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	jmp 26f
25:
26:
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
28:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
29:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 28b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
210:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
211:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 210b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+212]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha256_shani_sha1_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+208]
	mov eax, DWORD PTR [esp+176]
	sub eax, 58
	sbb ebx, ebx
	cmp eax, DWORD PTR [esp+200]
	sbb edx, edx
	or ebx, edx
	test ebx, ebx
	jne 20f
	mov esi, ebp
	add esi, 1024
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
22:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 22b
	mov esi, DWORD PTR [esp+204]
	mov ebx, ebp
	add ebx, 1025
	mov ecx, 28
23:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 23b
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+188]
	mov ecx, DWORD PTR [esp+192]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+192]
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, ebp
	add esi, 832
	mov ebx, ebp
	add ebx, 1053
	mov ecx, 28
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 24b
	mov ebx, ebp
	add ebx, 1024
	add ebx, DWORD PTR [esp+176]
	sub ebx, DWORD PTR [esp+200]
	sub ebx, 1
	mov eax, 1
	mov BYTE PTR [ebx], al
	add ebx, 1
	mov esi, DWORD PTR [esp+196]
	mov ecx, DWORD PTR [esp+200]
	test ecx, ecx
	je 25f
27:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 27b
	jmp 26f
25:
26:
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
28:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
29:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 29b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 28b
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+176]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
210:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
211:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 210b
	mov eax, DWORD PTR [esp+164]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+220]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+20], eax
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+28], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+212]
	sub eax, 1024
	mov DWORD PTR [esp+36], eax
	call {vg_rsa_public_precomputed_checked}
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+176]
	mov eax, 0
212:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 212b
	mov eax, 0
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+248]
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+252]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 58
	jb 20f
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
22:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
23:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 23b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 22b
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
24:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
25:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 25b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 24b
	mov esi, ebp
	add esi, 1053
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 28
26:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1081
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
27:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 27b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
28:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 28b
	mov esi, ebp
	add esi, 1081
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
210:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
211:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 210b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
212:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 212b
	mov eax, DWORD PTR [esp+180]
	sub eax, 58
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
213:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 213b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha1_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+248]
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+252]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 58
	jb 20f
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
22:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
23:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 23b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 22b
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
24:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
25:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 25b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 24b
	mov esi, ebp
	add esi, 1053
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 28
26:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1081
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
27:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 27b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
28:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 28b
	mov esi, ebp
	add esi, 1081
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
210:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
211:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 210b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
212:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 212b
	mov eax, DWORD PTR [esp+180]
	sub eax, 58
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
213:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 213b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha256_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+248]
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+252]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 58
	jb 20f
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
22:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
23:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 23b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 22b
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
24:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
25:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 25b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 24b
	mov esi, ebp
	add esi, 1053
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 28
26:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1081
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
27:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 27b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
28:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 28b
	mov esi, ebp
	add esi, 1081
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
210:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
211:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 210b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
212:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 212b
	mov eax, DWORD PTR [esp+180]
	sub eax, 58
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
213:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 213b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6

vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha256_shani_sha1_shani:
	push ebx
	push ebp
	push esi
	push edi
	lea esp, [esp-144]
	mov ebp, DWORD PTR [esp+248]
	mov eax, ebp
	add eax, 1024
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+176]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+184]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+188]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+240]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+180]
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+192]
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+36], eax
	mov eax, DWORD PTR [esp+200]
	mov DWORD PTR [esp+40], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+44], eax
	mov eax, DWORD PTR [esp+208]
	mov DWORD PTR [esp+48], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+52], eax
	mov eax, DWORD PTR [esp+216]
	mov DWORD PTR [esp+56], eax
	mov eax, DWORD PTR [esp+204]
	mov DWORD PTR [esp+60], eax
	mov eax, DWORD PTR [esp+224]
	mov DWORD PTR [esp+64], eax
	mov eax, DWORD PTR [esp+196]
	mov DWORD PTR [esp+68], eax
	mov eax, ebp
	add eax, 8192
	mov DWORD PTR [esp+72], eax
	mov eax, DWORD PTR [esp+252]
	sub eax, 1024
	mov DWORD PTR [esp+76], eax
	call {vg_rsa_private_checked}
	mov DWORD PTR [esp+96], eax
	mov eax, DWORD PTR [esp+180]
	cmp eax, 58
	jb 20f
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha224_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+232]
	mov ecx, DWORD PTR [esp+236]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha256_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+236]
	mov ecx, 0
	mov edx, ebp
	add edx, 896
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha256_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+88], eax
	mov eax, 28
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+80], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
22:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
23:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 23b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 22b
	mov eax, ebp
	add eax, 1053
	mov DWORD PTR [esp+88], eax
	mov eax, DWORD PTR [esp+180]
	sub eax, 29
	mov DWORD PTR [esp+92], eax
	mov eax, ebp
	add eax, 1025
	mov DWORD PTR [esp+80], eax
	mov eax, 28
	mov DWORD PTR [esp+84], eax
	mov eax, 0
	mov DWORD PTR [esp+104], eax
	mov DWORD PTR [esp+108], eax
24:
	mov ebx, ebp
	add ebx, 512
	push ebx
	call {vg_sha1_init}
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov edi, 0
	mov eax, 0
	mov edx, DWORD PTR [esp+80]
	mov ecx, DWORD PTR [esp+84]
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+104]
	bswap eax
	mov DWORD PTR [ebp+768], eax
	mov ebx, ebp
	add ebx, 512
	mov edi, DWORD PTR [esp+84]
	mov eax, 0
	mov edx, ebp
	add edx, 768
	mov ecx, 4
	push ebp
	push ecx
	push edx
	push eax
	push edi
	push ebx
	call {vg_sha1_update_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 512
	mov eax, DWORD PTR [esp+84]
	add eax, 4
	mov ecx, 0
	mov edx, ebp
	add edx, 832
	push ebp
	push edx
	push ecx
	push eax
	push ebx
	call {vg_sha1_finalize_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edi, DWORD PTR [esp+88]
	add edi, DWORD PTR [esp+108]
	mov esi, ebp
	add esi, 832
	mov ecx, DWORD PTR [esp+92]
	sub ecx, DWORD PTR [esp+108]
	mov eax, ecx
	sub eax, 20
	sbb edx, edx
	and eax, edx
	add eax, 20
	mov ecx, eax
25:
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [esi]
	xor eax, edx
	mov BYTE PTR [edi], al
	add edi, 1
	add esi, 1
	sub ecx, 1
	jne 25b
	mov eax, DWORD PTR [esp+104]
	add eax, 1
	mov DWORD PTR [esp+104], eax
	mov eax, DWORD PTR [esp+108]
	add eax, 20
	mov DWORD PTR [esp+108], eax
	cmp eax, DWORD PTR [esp+92]
	jb 24b
	mov esi, ebp
	add esi, 1053
	mov edi, ebp
	add edi, 896
	mov edx, 0
	mov ecx, 28
26:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	or edx, eax
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	mov esi, ebp
	add esi, 1024
	movzx eax, BYTE PTR [esi]
	or edx, eax
	mov DWORD PTR [esp+112], edx
	mov esi, ebp
	add esi, 1081
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
	mov edi, 0
	mov eax, 0
	mov DWORD PTR [esp+116], eax
	mov DWORD PTR [esp+140], eax
	mov ebx, 0
	sub ebx, 1
27:
	movzx eax, BYTE PTR [esi]
	mov edx, eax
	sub edx, 1
	sbb edx, edx
	xor edx, -1
	and edx, ebx
	and eax, edx
	mov ebp, DWORD PTR [esp+140]
	or ebp, eax
	mov DWORD PTR [esp+140], ebp
	mov eax, edi
	and eax, edx
	mov ebp, DWORD PTR [esp+116]
	or ebp, eax
	mov DWORD PTR [esp+116], ebp
	xor edx, -1
	and ebx, edx
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 27b
	mov ebp, DWORD PTR [esp+248]
	mov eax, DWORD PTR [esp+112]
	mov edx, DWORD PTR [esp+140]
	xor edx, 1
	or eax, edx
	shr ebx, 31
	or eax, ebx
	mov DWORD PTR [esp+112], eax
	mov esi, ebp
	add esi, 2048
	mov ecx, 2048
	mov eax, 0
28:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 28b
	mov esi, ebp
	add esi, 1081
	mov ebx, ebp
	add ebx, 2048
	mov ecx, DWORD PTR [esp+180]
	sub ecx, 57
29:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [ebx], al
	add ebx, 1
	add esi, 1
	sub ecx, 1
	cmp ecx, 0
	jne 29b
	mov eax, DWORD PTR [esp+116]
	add eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, 1
	mov DWORD PTR [esp+124], eax
	mov eax, 10
	mov DWORD PTR [esp+128], eax
210:
	mov esi, ebp
	add esi, 2048
	mov edi, esi
	add edi, DWORD PTR [esp+124]
	mov eax, DWORD PTR [esp+120]
	and eax, 1
	mov edx, 0
	sub edx, eax
	mov ecx, 1024
211:
	movzx eax, BYTE PTR [esi]
	movzx ebx, BYTE PTR [edi]
	xor ebx, eax
	and ebx, edx
	xor eax, ebx
	mov BYTE PTR [esi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 211b
	mov eax, DWORD PTR [esp+120]
	shr eax, 1
	mov DWORD PTR [esp+120], eax
	mov eax, DWORD PTR [esp+124]
	add eax, eax
	mov DWORD PTR [esp+124], eax
	mov eax, DWORD PTR [esp+128]
	sub eax, 1
	mov DWORD PTR [esp+128], eax
	jne 210b
	mov eax, DWORD PTR [esp+96]
	xor eax, 1
	or eax, DWORD PTR [esp+112]
	cmp eax, 1
	sbb eax, eax
	mov DWORD PTR [esp+100], eax
	mov esi, ebp
	add esi, 2048
	mov edi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov edx, DWORD PTR [esp+100]
212:
	movzx eax, BYTE PTR [esi]
	and eax, edx
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 212b
	mov eax, DWORD PTR [esp+180]
	sub eax, 58
	sub eax, DWORD PTR [esp+116]
	and eax, DWORD PTR [esp+100]
	mov esi, DWORD PTR [esp+172]
	mov DWORD PTR [esi], eax
	mov eax, 0
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
	mov edx, DWORD PTR [esp+100]
	and edx, 1
	or eax, edx
	jmp 21f
20:
	mov esi, DWORD PTR [esp+164]
	mov ecx, DWORD PTR [esp+180]
	mov eax, 0
213:
	mov BYTE PTR [esi], al
	add esi, 1
	sub ecx, 1
	jne 213b
	mov esi, DWORD PTR [esp+172]
	mov eax, 0
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esp+96]
	xor eax, 2
	cmp eax, 1
	sbb eax, eax
	and eax, 2
21:
	lea esp, [esp+144]
	mov edi, DWORD PTR [esp]
	mov esi, DWORD PTR [esp+4]
	mov ebp, DWORD PTR [esp+8]
	pop ebx
	pop ebx
	pop ebx
	pop ebx
	ret
	.p2align 6
