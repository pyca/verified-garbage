// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys_aesni:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
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
	mov DWORD PTR [ebx+16], eax
	mov DWORD PTR [ebx+20], ecx
	mov DWORD PTR [ebx+24], edx
	mov DWORD PTR [ebx+28], esi
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6

vg_cmac_aes_update_aesni:
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
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+24]
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [esi]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [esi+4]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [esi+8]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [esi+12]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
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

vg_cmac_aes_finalize_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+20]
	cmp ecx, 16
	je 20f
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov edi, ebp
	add edi, 2048
	mov esi, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	test ecx, ecx
	je 22f
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov eax, 128
	mov BYTE PTR [edi], al
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ebp+2048]
	mov ecx, DWORD PTR [edx+256]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebp+2052]
	mov ecx, DWORD PTR [edx+260]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebp+2056]
	mov ecx, DWORD PTR [edx+264]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebp+2060]
	mov ecx, DWORD PTR [edx+268]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
	jmp 21f
20:
	mov ebx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [edx+240]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [edx+244]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [edx+248]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [edx+252]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
21:
	mov ebx, DWORD PTR [esp+12]
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
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
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
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6

vg_cmac_aes_init_aesni:
	lea esp, [esp-2324]
	mov eax, DWORD PTR [esp+2328]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2332]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2336]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+4]
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
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	shr ecx, 2
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
	mov edx, DWORD PTR [esp+4]
	mov eax, 0
	mov DWORD PTR [edx+272], eax
	mov DWORD PTR [edx+276], eax
	mov DWORD PTR [edx+280], eax
	mov DWORD PTR [edx+284], eax
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2324]
	ret
	.p2align 6

vg_cmac_aes_absorb_aesni:
	lea esp, [esp-2336]
	mov eax, DWORD PTR [esp+2340]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2344]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2348]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2352]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2356]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2360]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 15
	add eax, 1
	jmp 21f
20:
21:
	mov ecx, 16
	sub ecx, eax
	mov edx, DWORD PTR [esp+24]
	cmp edx, ecx
	jb 22f
	jmp 23f
22:
	mov ecx, edx
23:
	mov ebp, ecx
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+4]
	add edi, 288
	add edi, eax
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov esi, 0
	mov edx, DWORD PTR [esp+24]
	sub edx, ebp
	je 27f
	mov esi, 1
	jmp 28f
27:
28:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, eax
	add edx, 272
	mov ebx, eax
	add ebx, 288
	mov edi, DWORD PTR [esp+28]
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
	mov ecx, 0
	mov ebx, DWORD PTR [esp+4]
	add ebx, 288
	mov edx, DWORD PTR [esp+24]
	sub edx, ebp
	je 29f
	mov ecx, edx
	sub ecx, 1
	mov eax, ecx
	and eax, 15
	sub ecx, eax
	mov ebx, DWORD PTR [esp+20]
	add ebx, ebp
	jmp 210f
29:
210:
	mov esi, ecx
	shr esi, 4
	add ebp, ecx
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, eax
	add edx, 272
	mov edi, DWORD PTR [esp+28]
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
	mov esi, DWORD PTR [esp+20]
	add esi, ebp
	mov edi, DWORD PTR [esp+4]
	add edi, 288
	mov ecx, DWORD PTR [esp+24]
	sub ecx, ebp
	test ecx, ecx
	je 211f
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2336]
	ret
	.p2align 6

vg_cmac_aes_finish_aesni:
	lea esp, [esp-2332]
	mov eax, DWORD PTR [esp+2336]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2340]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2344]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2348]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2352]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov esi, DWORD PTR [esp+4]
	add esi, 272
	mov edi, DWORD PTR [esp+20]
	mov ecx, 16
	test ecx, ecx
	je 20f
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	or ecx, esi
	je 23f
	sub esi, 1
	and esi, 15
	add esi, 1
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+20]
	mov ebx, eax
	add ebx, 288
	mov edi, DWORD PTR [esp+24]
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
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2332]
	ret
	.p2align 6

vg_cmac_aes_subkeys:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
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
	mov DWORD PTR [ebx+16], eax
	mov DWORD PTR [ebx+20], ecx
	mov DWORD PTR [ebx+24], edx
	mov DWORD PTR [ebx+28], esi
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6

vg_cmac_aes_update:
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
	mov ebx, DWORD PTR [esp+12]
	mov ebp, DWORD PTR [esp+24]
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [esi]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [esi+4]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [esi+8]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [esi+12]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
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

vg_cmac_aes_finalize:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+20]
	cmp ecx, 16
	je 20f
	mov eax, 0
	mov DWORD PTR [ebp+2048], eax
	mov DWORD PTR [ebp+2052], eax
	mov DWORD PTR [ebp+2056], eax
	mov DWORD PTR [ebp+2060], eax
	mov edi, ebp
	add edi, 2048
	mov esi, DWORD PTR [esp+16]
	mov ecx, DWORD PTR [esp+20]
	test ecx, ecx
	je 22f
24:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 24b
	jmp 23f
22:
23:
	mov eax, 128
	mov BYTE PTR [edi], al
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ebp+2048]
	mov ecx, DWORD PTR [edx+256]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebp+2052]
	mov ecx, DWORD PTR [edx+260]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebp+2056]
	mov ecx, DWORD PTR [edx+264]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebp+2060]
	mov ecx, DWORD PTR [edx+268]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
	jmp 21f
20:
	mov ebx, DWORD PTR [esp+16]
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ebx]
	mov ecx, DWORD PTR [edx+240]
	xor eax, ecx
	mov DWORD PTR [ebp+2048], eax
	mov eax, DWORD PTR [ebx+4]
	mov ecx, DWORD PTR [edx+244]
	xor eax, ecx
	mov DWORD PTR [ebp+2052], eax
	mov eax, DWORD PTR [ebx+8]
	mov ecx, DWORD PTR [edx+248]
	xor eax, ecx
	mov DWORD PTR [ebp+2056], eax
	mov eax, DWORD PTR [ebx+12]
	mov ecx, DWORD PTR [edx+252]
	xor eax, ecx
	mov DWORD PTR [ebp+2060], eax
21:
	mov ebx, DWORD PTR [esp+12]
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
	mov eax, 0
	mov DWORD PTR [ebx], eax
	mov DWORD PTR [ebx+4], eax
	mov DWORD PTR [ebx+8], eax
	mov DWORD PTR [ebx+12], eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, ebp
	add edx, 2048
	mov edi, 1
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
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	ret
	.p2align 6

vg_cmac_aes_init:
	lea esp, [esp-2324]
	mov eax, DWORD PTR [esp+2328]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2332]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2336]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov eax, DWORD PTR [esp+8]
	mov ecx, DWORD PTR [esp+12]
	mov edx, DWORD PTR [esp+4]
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
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+12]
	shr ecx, 2
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
	mov edx, DWORD PTR [esp+4]
	mov eax, 0
	mov DWORD PTR [edx+272], eax
	mov DWORD PTR [edx+276], eax
	mov DWORD PTR [edx+280], eax
	mov DWORD PTR [edx+284], eax
	mov eax, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2324]
	ret
	.p2align 6

vg_cmac_aes_absorb:
	lea esp, [esp-2336]
	mov eax, DWORD PTR [esp+2340]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2344]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2348]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2352]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2356]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+2360]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov eax, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	or ecx, eax
	je 20f
	sub eax, 1
	and eax, 15
	add eax, 1
	jmp 21f
20:
21:
	mov ecx, 16
	sub ecx, eax
	mov edx, DWORD PTR [esp+24]
	cmp edx, ecx
	jb 22f
	jmp 23f
22:
	mov ecx, edx
23:
	mov ebp, ecx
	mov esi, DWORD PTR [esp+20]
	mov edi, DWORD PTR [esp+4]
	add edi, 288
	add edi, eax
	test ecx, ecx
	je 24f
26:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 26b
	jmp 25f
24:
25:
	mov esi, 0
	mov edx, DWORD PTR [esp+24]
	sub edx, ebp
	je 27f
	mov esi, 1
	jmp 28f
27:
28:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, eax
	add edx, 272
	mov ebx, eax
	add ebx, 288
	mov edi, DWORD PTR [esp+28]
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
	mov ecx, 0
	mov ebx, DWORD PTR [esp+4]
	add ebx, 288
	mov edx, DWORD PTR [esp+24]
	sub edx, ebp
	je 29f
	mov ecx, edx
	sub ecx, 1
	mov eax, ecx
	and eax, 15
	sub ecx, eax
	mov ebx, DWORD PTR [esp+20]
	add ebx, ebp
	jmp 210f
29:
210:
	mov esi, ecx
	shr esi, 4
	add ebp, ecx
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, eax
	add edx, 272
	mov edi, DWORD PTR [esp+28]
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
	mov esi, DWORD PTR [esp+20]
	add esi, ebp
	mov edi, DWORD PTR [esp+4]
	add edi, 288
	mov ecx, DWORD PTR [esp+24]
	sub ecx, ebp
	test ecx, ecx
	je 211f
213:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 213b
	jmp 212f
211:
212:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2336]
	ret
	.p2align 6

vg_cmac_aes_finish:
	lea esp, [esp-2332]
	mov eax, DWORD PTR [esp+2336]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+2340]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+2344]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+2348]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+2352]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2176], ebx
	mov DWORD PTR [eax+2180], esi
	mov DWORD PTR [eax+2184], edi
	mov DWORD PTR [eax+2188], ebp
	mov esi, DWORD PTR [esp+4]
	add esi, 272
	mov edi, DWORD PTR [esp+20]
	mov ecx, 16
	test ecx, ecx
	je 20f
22:
	movzx eax, BYTE PTR [esi]
	mov BYTE PTR [edi], al
	add esi, 1
	add edi, 1
	sub ecx, 1
	jne 22b
	jmp 21f
20:
21:
	mov esi, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [esp+16]
	or ecx, esi
	je 23f
	sub esi, 1
	and esi, 15
	add esi, 1
	jmp 24f
23:
24:
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+20]
	mov ebx, eax
	add ebx, 288
	mov edi, DWORD PTR [esp+24]
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
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2176]
	mov esi, DWORD PTR [eax+2180]
	mov edi, DWORD PTR [eax+2184]
	mov ebp, DWORD PTR [eax+2188]
	lea esp, [esp+2332]
	ret
	.p2align 6
