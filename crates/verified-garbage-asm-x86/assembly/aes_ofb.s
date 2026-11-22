// The functions of `src/aes_ofb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ofb_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov edi, DWORD PTR [esp+20]
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [edx]
22:
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	cmp ecx, 10
	je 23f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 25f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 26f
25:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
26:
	jmp 24f
23:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
24:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm7, xmm0
	movdqu XMMWORD PTR [esi], xmm7
	add esi, 16
	sub edi, 1
	jne 22b
	movdqu XMMWORD PTR [edx], xmm0
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+24]
	mov ebx, DWORD PTR [eax+2064]
	mov esi, DWORD PTR [eax+2068]
	mov edi, DWORD PTR [eax+2072]
	mov ebp, DWORD PTR [eax+2076]
	mov ecx, DWORD PTR [esp+24]
	mov eax, 0
	mov DWORD PTR [ecx+2048], eax
	mov DWORD PTR [ecx+2052], eax
	mov DWORD PTR [ecx+2056], eax
	mov DWORD PTR [ecx+2060], eax
	mov eax, 0
	mov DWORD PTR [ecx+2064], eax
	mov DWORD PTR [ecx+2068], eax
	mov DWORD PTR [ecx+2072], eax
	mov DWORD PTR [ecx+2076], eax
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_ofb_final_aesni:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
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
	call {vg_aes_ofb_aesni_core}
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
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
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
	mov ebx, DWORD PTR [esp+12]
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
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_ofb:
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
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
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
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-24]
	movdqu XMMWORD PTR [esp], xmm0
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	lea esp, [esp+24]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6

vg_aes_ofb_final:
	lea esp, [esp-48]
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+64]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+72]
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
	call {vg_aes_ofb_core}
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
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebx, DWORD PTR [esp+12]
	mov edi, 1
	mov ebp, DWORD PTR [esp+24]
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
	mov ebx, DWORD PTR [esp+12]
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
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+32], xmm0
	lea esp, [esp+48]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-100]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	mov DWORD PTR [esp+96], ecx
	lea esp, [esp+100]
	mov eax, 0
	mov edx, 0
	xor ecx, ecx
	pxor xmm0, xmm0
	pxor xmm1, xmm1
	pxor xmm2, xmm2
	pxor xmm3, xmm3
	pxor xmm4, xmm4
	pxor xmm5, xmm5
	pxor xmm6, xmm6
	pxor xmm7, xmm7
	ret
	.p2align 6
