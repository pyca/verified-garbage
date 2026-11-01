// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
