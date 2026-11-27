// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_encrypt_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, DWORD PTR [esp+16]
	mov ebp, DWORD PTR [esp+20]
	mov edx, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [edx]
22:
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm0, xmm1
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
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub ebp, 1
	jne 22b
	mov edx, DWORD PTR [esp+12]
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

vg_aes_cbc_decrypt_aesni:
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
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
	call {vg_aes_cbc_decrypt_unwiped_aesni}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp], eax
	mov eax, 240
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+44]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-72]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	lea esp, [esp+72]
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

vg_aes_cbc_encrypt_ssse3:
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
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
	call {vg_aes_cbc_encrypt_unwiped_ssse3}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp], eax
	mov eax, 480
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+44]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-72]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	lea esp, [esp+72]
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

vg_aes_cbc_decrypt_ssse3:
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
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
	call {vg_aes_cbc_decrypt_unwiped_ssse3}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp], eax
	mov eax, 720
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+44]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1156]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	mov DWORD PTR [esp+1152], ecx
	lea esp, [esp+1156]
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

vg_aes_cbc_encrypt:
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
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
	call {vg_aes_cbc_encrypt_unwiped}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+44]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-72]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	lea esp, [esp+72]
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

vg_aes_cbc_decrypt:
	lea esp, [esp-44]
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp], eax
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
	call {vg_aes_cbc_decrypt_unwiped}
	mov DWORD PTR [esp+24], eax
	mov DWORD PTR [esp+28], edx
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp], eax
	mov eax, 2048
	mov DWORD PTR [esp+4], eax
	call {vg_zeroize_core}
	mov eax, DWORD PTR [esp+24]
	mov edx, DWORD PTR [esp+28]
	lea esp, [esp+44]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1156]
	movdqu XMMWORD PTR [esp], xmm0
	movdqu XMMWORD PTR [esp+16], xmm0
	movdqu XMMWORD PTR [esp+32], xmm0
	movdqu XMMWORD PTR [esp+48], xmm0
	movdqu XMMWORD PTR [esp+64], xmm0
	movdqu XMMWORD PTR [esp+80], xmm0
	movdqu XMMWORD PTR [esp+96], xmm0
	movdqu XMMWORD PTR [esp+112], xmm0
	movdqu XMMWORD PTR [esp+128], xmm0
	movdqu XMMWORD PTR [esp+144], xmm0
	movdqu XMMWORD PTR [esp+160], xmm0
	movdqu XMMWORD PTR [esp+176], xmm0
	movdqu XMMWORD PTR [esp+192], xmm0
	movdqu XMMWORD PTR [esp+208], xmm0
	movdqu XMMWORD PTR [esp+224], xmm0
	movdqu XMMWORD PTR [esp+240], xmm0
	movdqu XMMWORD PTR [esp+256], xmm0
	movdqu XMMWORD PTR [esp+272], xmm0
	movdqu XMMWORD PTR [esp+288], xmm0
	movdqu XMMWORD PTR [esp+304], xmm0
	movdqu XMMWORD PTR [esp+320], xmm0
	movdqu XMMWORD PTR [esp+336], xmm0
	movdqu XMMWORD PTR [esp+352], xmm0
	movdqu XMMWORD PTR [esp+368], xmm0
	movdqu XMMWORD PTR [esp+384], xmm0
	movdqu XMMWORD PTR [esp+400], xmm0
	movdqu XMMWORD PTR [esp+416], xmm0
	movdqu XMMWORD PTR [esp+432], xmm0
	movdqu XMMWORD PTR [esp+448], xmm0
	movdqu XMMWORD PTR [esp+464], xmm0
	movdqu XMMWORD PTR [esp+480], xmm0
	movdqu XMMWORD PTR [esp+496], xmm0
	movdqu XMMWORD PTR [esp+512], xmm0
	movdqu XMMWORD PTR [esp+528], xmm0
	movdqu XMMWORD PTR [esp+544], xmm0
	movdqu XMMWORD PTR [esp+560], xmm0
	movdqu XMMWORD PTR [esp+576], xmm0
	movdqu XMMWORD PTR [esp+592], xmm0
	movdqu XMMWORD PTR [esp+608], xmm0
	movdqu XMMWORD PTR [esp+624], xmm0
	movdqu XMMWORD PTR [esp+640], xmm0
	movdqu XMMWORD PTR [esp+656], xmm0
	movdqu XMMWORD PTR [esp+672], xmm0
	movdqu XMMWORD PTR [esp+688], xmm0
	movdqu XMMWORD PTR [esp+704], xmm0
	movdqu XMMWORD PTR [esp+720], xmm0
	movdqu XMMWORD PTR [esp+736], xmm0
	movdqu XMMWORD PTR [esp+752], xmm0
	movdqu XMMWORD PTR [esp+768], xmm0
	movdqu XMMWORD PTR [esp+784], xmm0
	movdqu XMMWORD PTR [esp+800], xmm0
	movdqu XMMWORD PTR [esp+816], xmm0
	movdqu XMMWORD PTR [esp+832], xmm0
	movdqu XMMWORD PTR [esp+848], xmm0
	movdqu XMMWORD PTR [esp+864], xmm0
	movdqu XMMWORD PTR [esp+880], xmm0
	movdqu XMMWORD PTR [esp+896], xmm0
	movdqu XMMWORD PTR [esp+912], xmm0
	movdqu XMMWORD PTR [esp+928], xmm0
	movdqu XMMWORD PTR [esp+944], xmm0
	movdqu XMMWORD PTR [esp+960], xmm0
	movdqu XMMWORD PTR [esp+976], xmm0
	movdqu XMMWORD PTR [esp+992], xmm0
	movdqu XMMWORD PTR [esp+1008], xmm0
	movdqu XMMWORD PTR [esp+1024], xmm0
	movdqu XMMWORD PTR [esp+1040], xmm0
	movdqu XMMWORD PTR [esp+1056], xmm0
	movdqu XMMWORD PTR [esp+1072], xmm0
	movdqu XMMWORD PTR [esp+1088], xmm0
	movdqu XMMWORD PTR [esp+1104], xmm0
	movdqu XMMWORD PTR [esp+1120], xmm0
	movdqu XMMWORD PTR [esp+1136], xmm0
	mov DWORD PTR [esp+1152], ecx
	lea esp, [esp+1156]
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
