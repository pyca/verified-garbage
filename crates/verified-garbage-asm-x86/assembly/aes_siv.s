// The functions of `src/aes_siv.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init_aesni:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 1
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 6
	mov edx, eax
	add edx, 240
	mov ebx, DWORD PTR [esp+16]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_subkeys_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 1
	mov eax, DWORD PTR [esp+4]
	add eax, ecx
	mov edx, DWORD PTR [esp+12]
	add edx, 272
	mov ebx, DWORD PTR [esp+16]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2580]
	ret
	.p2align 6

vg_aes_siv_encrypt_aesni:
	lea esp, [esp-2612]
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, 0
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+28], eax
	mov eax, 0
	mov DWORD PTR [ebp+2560], eax
	mov DWORD PTR [ebp+2564], eax
	mov DWORD PTR [ebp+2568], eax
	mov DWORD PTR [ebp+2572], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 2560
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 16
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+188]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+200], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+204], ecx
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov ecx, 0
	mov eax, DWORD PTR [ebp+204]
	test eax, eax
	je 23f
	mov ecx, eax
	sub ecx, 1
	and ecx, -16
	jmp 24f
23:
24:
	mov DWORD PTR [ebp+208], ecx
	mov esi, ecx
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+200]
	add ebx, DWORD PTR [ebp+208]
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 2560
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 2560
	mov edx, ebp
	add edx, 2560
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [ebp+184]
	add eax, 8
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [ebp+188]
	sub eax, 1
	mov DWORD PTR [ebp+188], eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+204], eax
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 16
	jb 25f
	mov eax, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 27f
	mov eax, ecx
	sub eax, 1
	and eax, -16
	sub eax, 16
	jmp 28f
27:
28:
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+200]
	add edi, eax
	sub ecx, eax
	mov edx, ebp
	add edx, 32
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	sub edx, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+2560]
	xor eax, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+2564]
	xor eax, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+2568]
	xor eax, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [ebp+2572]
	xor eax, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov esi, DWORD PTR [ebp+208]
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 210f
	mov esi, 1
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+212], esi
	mov ebx, ebp
	add ebx, 32
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+212]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	sub esi, eax
	mov ebx, ebp
	add ebx, 32
	add ebx, eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 26f
25:
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov edi, DWORD PTR [ebp+200]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+204]
	test ecx, ecx
	je 212f
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	jmp 213f
212:
213:
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	mov eax, 128
	mov BYTE PTR [edx+32], al
	mov eax, DWORD PTR [ebp+2560]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+2564]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+2568]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+2572]
	mov DWORD PTR [ebp+172], eax
	mov ebx, ebp
	add ebx, 160
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 160
	mov edx, ebp
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [edx+32]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [edx+36]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [edx+40]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [edx+44]
	mov DWORD PTR [edx+44], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 32
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
26:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	and eax, -129
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, -129
	mov DWORD PTR [ebp+108], eax
	mov edi, DWORD PTR [ebp+196]
	shr edi, 4
	test edi, edi
	je 215f
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, DWORD PTR [ebp+192]
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	jmp 216f
215:
216:
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	je 217f
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	mov edx, ebp
	add edx, 80
	mov edi, DWORD PTR [ebp+192]
	add edi, DWORD PTR [ebp+196]
	sub edi, ecx
219:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	jmp 218f
217:
218:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [esp+28]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2612]
	ret
	.p2align 6

vg_aes_siv_decrypt_aesni:
	lea esp, [esp-2612]
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, 0
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+28], eax
	mov eax, 0
	mov DWORD PTR [ebp+2560], eax
	mov DWORD PTR [ebp+2564], eax
	mov DWORD PTR [ebp+2568], eax
	mov DWORD PTR [ebp+2572], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 2560
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 16
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+188]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+200], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+204], ecx
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov ecx, 0
	mov eax, DWORD PTR [ebp+204]
	test eax, eax
	je 23f
	mov ecx, eax
	sub ecx, 1
	and ecx, -16
	jmp 24f
23:
24:
	mov DWORD PTR [ebp+208], ecx
	mov esi, ecx
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+200]
	add ebx, DWORD PTR [ebp+208]
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 2560
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 2560
	mov edx, ebp
	add edx, 2560
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [ebp+184]
	add eax, 8
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [ebp+188]
	sub eax, 1
	mov DWORD PTR [ebp+188], eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+204], eax
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	and eax, -129
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, -129
	mov DWORD PTR [ebp+108], eax
	mov edi, DWORD PTR [ebp+196]
	shr edi, 4
	test edi, edi
	je 25f
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, DWORD PTR [ebp+192]
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	jmp 26f
25:
26:
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	je 27f
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	mov edx, ebp
	add edx, 80
	mov edi, DWORD PTR [ebp+192]
	add edi, DWORD PTR [ebp+196]
	sub edi, ecx
29:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	jmp 28f
27:
28:
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+204], eax
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 16
	jb 210f
	mov eax, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 212f
	mov eax, ecx
	sub eax, 1
	and eax, -16
	sub eax, 16
	jmp 213f
212:
213:
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+200]
	add edi, eax
	sub ecx, eax
	mov edx, ebp
	add edx, 32
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	sub edx, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+2560]
	xor eax, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+2564]
	xor eax, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+2568]
	xor eax, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [ebp+2572]
	xor eax, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov esi, DWORD PTR [ebp+208]
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 215f
	mov esi, 1
	jmp 216f
215:
216:
	mov DWORD PTR [ebp+212], esi
	mov ebx, ebp
	add ebx, 32
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+212]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	sub esi, eax
	mov ebx, ebp
	add ebx, 32
	add ebx, eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 211f
210:
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov edi, DWORD PTR [ebp+200]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+204]
	test ecx, ecx
	je 217f
219:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	jmp 218f
217:
218:
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	mov eax, 128
	mov BYTE PTR [edx+32], al
	mov eax, DWORD PTR [ebp+2560]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+2564]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+2568]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+2572]
	mov DWORD PTR [ebp+172], eax
	mov ebx, ebp
	add ebx, 160
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 160
	mov edx, ebp
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [edx+32]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [edx+36]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [edx+40]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [edx+44]
	mov DWORD PTR [edx+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 32
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
211:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+4]
	xor ecx, DWORD PTR [ebp+116]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+120]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+12]
	xor ecx, DWORD PTR [ebp+124]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+216], eax
	mov ecx, DWORD PTR [ebp+196]
	test ecx, ecx
	je 220f
	mov ebx, 0
	sub ebx, DWORD PTR [ebp+216]
	mov edi, DWORD PTR [ebp+192]
222:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 222b
	jmp 221f
220:
221:
	mov eax, DWORD PTR [ebp+216]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2612]
	ret
	.p2align 6

vg_aes_siv_init:
	lea esp, [esp-2580]
	mov eax, DWORD PTR [esp+2584]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2588]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2592]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 1
	mov edx, DWORD PTR [esp+12]
	mov ebx, DWORD PTR [esp+16]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 6
	mov edx, eax
	add edx, 240
	mov ebx, DWORD PTR [esp+16]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_subkeys}
	pop eax
	pop eax
	pop eax
	pop eax
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 1
	mov eax, DWORD PTR [esp+4]
	add eax, ecx
	mov edx, DWORD PTR [esp+12]
	add edx, 272
	mov ebx, DWORD PTR [esp+16]
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_expand_key_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2580]
	ret
	.p2align 6

vg_aes_siv_encrypt:
	lea esp, [esp-2612]
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, 0
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+28], eax
	mov eax, 0
	mov DWORD PTR [ebp+2560], eax
	mov DWORD PTR [ebp+2564], eax
	mov DWORD PTR [ebp+2568], eax
	mov DWORD PTR [ebp+2572], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 2560
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 16
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+188]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+200], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+204], ecx
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov ecx, 0
	mov eax, DWORD PTR [ebp+204]
	test eax, eax
	je 23f
	mov ecx, eax
	sub ecx, 1
	and ecx, -16
	jmp 24f
23:
24:
	mov DWORD PTR [ebp+208], ecx
	mov esi, ecx
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+200]
	add ebx, DWORD PTR [ebp+208]
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 2560
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 2560
	mov edx, ebp
	add edx, 2560
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [ebp+184]
	add eax, 8
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [ebp+188]
	sub eax, 1
	mov DWORD PTR [ebp+188], eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+204], eax
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 16
	jb 25f
	mov eax, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 27f
	mov eax, ecx
	sub eax, 1
	and eax, -16
	sub eax, 16
	jmp 28f
27:
28:
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+200]
	add edi, eax
	sub ecx, eax
	mov edx, ebp
	add edx, 32
29:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	sub edx, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+2560]
	xor eax, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+2564]
	xor eax, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+2568]
	xor eax, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [ebp+2572]
	xor eax, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov esi, DWORD PTR [ebp+208]
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 210f
	mov esi, 1
	jmp 211f
210:
211:
	mov DWORD PTR [ebp+212], esi
	mov ebx, ebp
	add ebx, 32
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+212]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	sub esi, eax
	mov ebx, ebp
	add ebx, 32
	add ebx, eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 26f
25:
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov edi, DWORD PTR [ebp+200]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+204]
	test ecx, ecx
	je 212f
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	jmp 213f
212:
213:
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	mov eax, 128
	mov BYTE PTR [edx+32], al
	mov eax, DWORD PTR [ebp+2560]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+2564]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+2568]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+2572]
	mov DWORD PTR [ebp+172], eax
	mov ebx, ebp
	add ebx, 160
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 160
	mov edx, ebp
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [edx+32]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [edx+36]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [edx+40]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [edx+44]
	mov DWORD PTR [edx+44], eax
	mov eax, 0
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], eax
	mov DWORD PTR [ebp+8], eax
	mov DWORD PTR [ebp+12], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 0
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 32
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
26:
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	and eax, -129
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, -129
	mov DWORD PTR [ebp+108], eax
	mov edi, DWORD PTR [ebp+196]
	shr edi, 4
	test edi, edi
	je 215f
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, DWORD PTR [ebp+192]
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	jmp 216f
215:
216:
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	je 217f
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	mov edx, ebp
	add edx, 80
	mov edi, DWORD PTR [ebp+192]
	add edi, DWORD PTR [ebp+196]
	sub edi, ecx
219:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	jmp 218f
217:
218:
	mov eax, DWORD PTR [ebp]
	mov ecx, DWORD PTR [ebp+4]
	mov edx, DWORD PTR [ebp+8]
	mov ebx, DWORD PTR [ebp+12]
	mov edi, DWORD PTR [esp+28]
	mov DWORD PTR [edi], eax
	mov DWORD PTR [edi+4], ecx
	mov DWORD PTR [edi+8], edx
	mov DWORD PTR [edi+12], ebx
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2612]
	ret
	.p2align 6

vg_aes_siv_decrypt:
	lea esp, [esp-2612]
	mov eax, DWORD PTR [esp+2616]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2620]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2624]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2628]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2632]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2636]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+2640]
	mov DWORD PTR [esp+28], eax
	mov eax, esp
	add eax, 36
	mov DWORD PTR [esp+32], eax
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov DWORD PTR [ebp+176], eax
	mov eax, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+180], eax
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [ebp+188], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [ebp+192], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [ebp+196], eax
	mov eax, 0
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], eax
	mov DWORD PTR [ebp+24], eax
	mov DWORD PTR [ebp+28], eax
	mov eax, 0
	mov DWORD PTR [ebp+2560], eax
	mov DWORD PTR [ebp+2564], eax
	mov DWORD PTR [ebp+2568], eax
	mov DWORD PTR [ebp+2572], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 2560
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 16
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+188]
	test eax, eax
	je 20f
22:
	mov eax, DWORD PTR [ebp+184]
	mov ecx, DWORD PTR [eax]
	mov DWORD PTR [ebp+200], ecx
	mov ecx, DWORD PTR [eax+4]
	mov DWORD PTR [ebp+204], ecx
	mov eax, 0
	mov DWORD PTR [ebp+144], eax
	mov DWORD PTR [ebp+148], eax
	mov DWORD PTR [ebp+152], eax
	mov DWORD PTR [ebp+156], eax
	mov ecx, 0
	mov eax, DWORD PTR [ebp+204]
	test eax, eax
	je 23f
	mov ecx, eax
	sub ecx, 1
	and ecx, -16
	jmp 24f
23:
24:
	mov DWORD PTR [ebp+208], ecx
	mov esi, ecx
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, DWORD PTR [ebp+200]
	add ebx, DWORD PTR [ebp+208]
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 144
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebx, ebp
	add ebx, 2560
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 2560
	mov edx, ebp
	add edx, 2560
	mov eax, DWORD PTR [ebp+144]
	xor eax, DWORD PTR [edx]
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [ebp+148]
	xor eax, DWORD PTR [edx+4]
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [ebp+152]
	xor eax, DWORD PTR [edx+8]
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [ebp+156]
	xor eax, DWORD PTR [edx+12]
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [ebp+184]
	add eax, 8
	mov DWORD PTR [ebp+184], eax
	mov eax, DWORD PTR [ebp+188]
	sub eax, 1
	mov DWORD PTR [ebp+188], eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+204], eax
	mov edi, DWORD PTR [esp+28]
	mov eax, DWORD PTR [edi]
	mov ecx, DWORD PTR [edi+4]
	mov edx, DWORD PTR [edi+8]
	mov ebx, DWORD PTR [edi+12]
	mov DWORD PTR [ebp], eax
	mov DWORD PTR [ebp+4], ecx
	mov DWORD PTR [ebp+8], edx
	mov DWORD PTR [ebp+12], ebx
	mov eax, DWORD PTR [ebp]
	mov DWORD PTR [ebp+96], eax
	mov eax, DWORD PTR [ebp+4]
	mov DWORD PTR [ebp+100], eax
	mov eax, DWORD PTR [ebp+8]
	and eax, -129
	mov DWORD PTR [ebp+104], eax
	mov eax, DWORD PTR [ebp+12]
	and eax, -129
	mov DWORD PTR [ebp+108], eax
	mov edi, DWORD PTR [ebp+196]
	shr edi, 4
	test edi, edi
	je 25f
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, DWORD PTR [ebp+192]
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	jmp 26f
25:
26:
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	je 27f
	mov eax, 0
	mov DWORD PTR [ebp+80], eax
	mov DWORD PTR [ebp+84], eax
	mov DWORD PTR [ebp+88], eax
	mov DWORD PTR [ebp+92], eax
	mov eax, DWORD PTR [ebp+176]
	add eax, 272
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 96
	mov ebx, ebp
	add ebx, 80
	mov edi, 1
	add ebp, 256
	push ebp
	push edi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_ctr32}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebp, 256
	mov ecx, DWORD PTR [ebp+196]
	and ecx, 15
	mov edx, ebp
	add edx, 80
	mov edi, DWORD PTR [ebp+192]
	add edi, DWORD PTR [ebp+196]
	sub edi, ecx
29:
	movzx eax, BYTE PTR [edx]
	movzx ebx, BYTE PTR [edi]
	xor eax, ebx
	mov BYTE PTR [edi], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 29b
	jmp 28f
27:
28:
	mov eax, DWORD PTR [ebp+192]
	mov DWORD PTR [ebp+200], eax
	mov eax, DWORD PTR [ebp+196]
	mov DWORD PTR [ebp+204], eax
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 16
	jb 210f
	mov eax, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 212f
	mov eax, ecx
	sub eax, 1
	and eax, -16
	sub eax, 16
	jmp 213f
212:
213:
	mov DWORD PTR [ebp+208], eax
	mov edi, DWORD PTR [ebp+200]
	add edi, eax
	sub ecx, eax
	mov edx, ebp
	add edx, 32
214:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 214b
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	sub edx, DWORD PTR [ebp+208]
	mov eax, DWORD PTR [ebp+2560]
	xor eax, DWORD PTR [edx+16]
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [ebp+2564]
	xor eax, DWORD PTR [edx+20]
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [ebp+2568]
	xor eax, DWORD PTR [edx+24]
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [ebp+2572]
	xor eax, DWORD PTR [edx+28]
	mov DWORD PTR [edx+28], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov esi, DWORD PTR [ebp+208]
	shr esi, 4
	mov ebx, DWORD PTR [ebp+200]
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 0
	mov ecx, DWORD PTR [ebp+204]
	cmp ecx, 17
	jb 215f
	mov esi, 1
	jmp 216f
215:
216:
	mov DWORD PTR [ebp+212], esi
	mov ebx, ebp
	add ebx, 32
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_update}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [ebp+212]
	add eax, eax
	add eax, eax
	add eax, eax
	add eax, eax
	mov esi, DWORD PTR [ebp+204]
	sub esi, DWORD PTR [ebp+208]
	sub esi, eax
	mov ebx, ebp
	add ebx, 32
	add ebx, eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	jmp 211f
210:
	mov eax, 0
	mov DWORD PTR [ebp+32], eax
	mov DWORD PTR [ebp+36], eax
	mov DWORD PTR [ebp+40], eax
	mov DWORD PTR [ebp+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+48], eax
	mov DWORD PTR [ebp+52], eax
	mov DWORD PTR [ebp+56], eax
	mov DWORD PTR [ebp+60], eax
	mov edi, DWORD PTR [ebp+200]
	mov edx, ebp
	add edx, 32
	mov ecx, DWORD PTR [ebp+204]
	test ecx, ecx
	je 217f
219:
	movzx eax, BYTE PTR [edi]
	mov BYTE PTR [edx], al
	add edi, 1
	add edx, 1
	sub ecx, 1
	jne 219b
	jmp 218f
217:
218:
	mov edx, ebp
	add edx, DWORD PTR [ebp+204]
	mov eax, 128
	mov BYTE PTR [edx+32], al
	mov eax, DWORD PTR [ebp+2560]
	mov DWORD PTR [ebp+160], eax
	mov eax, DWORD PTR [ebp+2564]
	mov DWORD PTR [ebp+164], eax
	mov eax, DWORD PTR [ebp+2568]
	mov DWORD PTR [ebp+168], eax
	mov eax, DWORD PTR [ebp+2572]
	mov DWORD PTR [ebp+172], eax
	mov ebx, ebp
	add ebx, 160
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [ebx+4]
	mov edx, DWORD PTR [ebx+8]
	mov esi, DWORD PTR [ebx+12]
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov edi, eax
	shr edi, 31
	mov ebp, 0
	sub ebp, edi
	and ebp, 135
	add eax, eax
	mov edi, ecx
	shr edi, 31
	or eax, edi
	add ecx, ecx
	mov edi, edx
	shr edi, 31
	or ecx, edi
	add edx, edx
	mov edi, esi
	shr edi, 31
	or edx, edi
	add esi, esi
	xor esi, ebp
	bswap eax
	bswap ecx
	bswap edx
	bswap esi
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], ecx
	mov DWORD PTR [ebx+8], edx
	mov DWORD PTR [ebx+12], esi
	mov ebp, ebx
	sub ebp, 160
	mov edx, ebp
	mov eax, DWORD PTR [ebp+160]
	xor eax, DWORD PTR [edx+32]
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [ebp+164]
	xor eax, DWORD PTR [edx+36]
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [ebp+168]
	xor eax, DWORD PTR [edx+40]
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [ebp+172]
	xor eax, DWORD PTR [edx+44]
	mov DWORD PTR [edx+44], eax
	mov eax, 0
	mov DWORD PTR [ebp+112], eax
	mov DWORD PTR [ebp+116], eax
	mov DWORD PTR [ebp+120], eax
	mov DWORD PTR [ebp+124], eax
	mov eax, DWORD PTR [ebp+176]
	mov ecx, DWORD PTR [ebp+180]
	mov edx, ebp
	add edx, 112
	mov edi, ebp
	add edi, 256
	mov ebx, ebp
	add ebx, 32
	mov esi, 16
	push edi
	push esi
	push ebx
	push edx
	push ecx
	push eax
	call {vg_cmac_aes_finalize}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
211:
	mov eax, DWORD PTR [ebp]
	xor eax, DWORD PTR [ebp+112]
	mov ecx, DWORD PTR [ebp+4]
	xor ecx, DWORD PTR [ebp+116]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+8]
	xor ecx, DWORD PTR [ebp+120]
	or eax, ecx
	mov ecx, DWORD PTR [ebp+12]
	xor ecx, DWORD PTR [ebp+124]
	or eax, ecx
	cmp eax, 1
	mov eax, 0
	adc eax, 0
	mov DWORD PTR [ebp+216], eax
	mov ecx, DWORD PTR [ebp+196]
	test ecx, ecx
	je 220f
	mov ebx, 0
	sub ebx, DWORD PTR [ebp+216]
	mov edi, DWORD PTR [ebp+192]
222:
	movzx edx, BYTE PTR [edi]
	and edx, ebx
	mov BYTE PTR [edi], dl
	add edi, 1
	sub ecx, 1
	jne 222b
	jmp 221f
220:
221:
	mov eax, DWORD PTR [ebp+216]
	mov ebx, DWORD PTR [ebp+128]
	mov esi, DWORD PTR [ebp+132]
	mov edi, DWORD PTR [ebp+136]
	mov ebp, DWORD PTR [ebp+140]
	lea esp, [esp+2612]
	ret
	.p2align 6
