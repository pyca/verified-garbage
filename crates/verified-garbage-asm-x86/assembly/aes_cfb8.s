// The functions of `src/aes_cfb8.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb8_encrypt_aesni:
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
	movzx eax, BYTE PTR [esi]
	movzx ecx, BYTE PTR [ebp+2048]
	xor eax, ecx
	mov BYTE PTR [esi], al
	mov ebx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [ebx+1]
	mov edx, DWORD PTR [ebx+5]
	mov edi, DWORD PTR [ebx+9]
	mov ebp, DWORD PTR [ebx+12]
	mov DWORD PTR [ebx], ecx
	mov DWORD PTR [ebx+4], edx
	mov DWORD PTR [ebx+8], edi
	mov DWORD PTR [ebx+11], ebp
	mov BYTE PTR [ebx+15], al
	add esi, 1
	mov eax, DWORD PTR [esp+20]
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

vg_aes_cfb8_decrypt_aesni:
	lea esp, [esp-1084]
	mov eax, DWORD PTR [esp+1088]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1092]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1096]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1100]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+1024], ebx
	mov DWORD PTR [eax+1028], esi
	mov DWORD PTR [eax+1032], edi
	mov DWORD PTR [eax+1036], ebp
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ebx, 64
	cmp edi, 64
	jb 23f
	jmp 24f
23:
	mov ebx, edi
24:
	mov ebp, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [ebp]
	mov eax, esi
	mov edx, DWORD PTR [esp+28]
	mov ecx, ebx
25:
	movdqu XMMWORD PTR [edx], xmm0
	movzx ebp, BYTE PTR [eax]
	movd xmm1, ebp
	psrldq xmm0, 1
	pslldq xmm1, 15
	por xmm0, xmm1
	add eax, 1
	add edx, 16
	sub ecx, 1
	jne 25b
	mov ebp, DWORD PTR [esp+12]
	movdqu XMMWORD PTR [ebp], xmm0
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+28]
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_aesni}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov ebp, ebx
26:
	movzx eax, BYTE PTR [esi]
	movzx ecx, BYTE PTR [edx]
	xor eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 16
	sub ebp, 1
	jne 26b
	sub edi, ebx
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+1024]
	mov esi, DWORD PTR [eax+1028]
	mov edi, DWORD PTR [eax+1032]
	mov ebp, DWORD PTR [eax+1036]
	lea esp, [esp+1084]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1108]
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
	mov DWORD PTR [esp+1104], ecx
	lea esp, [esp+1108]
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

vg_aes_cfb8_encrypt_ssse3:
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
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov ebp, DWORD PTR [esp+24]
	movzx eax, BYTE PTR [esi]
	movzx ecx, BYTE PTR [ebp+2048]
	xor eax, ecx
	mov BYTE PTR [esi], al
	mov ebx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [ebx+1]
	mov edx, DWORD PTR [ebx+5]
	mov edi, DWORD PTR [ebx+9]
	mov ebp, DWORD PTR [ebx+12]
	mov DWORD PTR [ebx], ecx
	mov DWORD PTR [ebx+4], edx
	mov DWORD PTR [ebx+8], edi
	mov DWORD PTR [ebx+11], ebp
	mov BYTE PTR [ebx+15], al
	add esi, 1
	mov eax, DWORD PTR [esp+20]
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

vg_aes_cfb8_decrypt_ssse3:
	lea esp, [esp-1084]
	mov eax, DWORD PTR [esp+1088]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1092]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1096]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1100]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+1024], ebx
	mov DWORD PTR [eax+1028], esi
	mov DWORD PTR [eax+1032], edi
	mov DWORD PTR [eax+1036], ebp
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ebx, 64
	cmp edi, 64
	jb 23f
	jmp 24f
23:
	mov ebx, edi
24:
	mov ebp, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [ebp]
	mov eax, esi
	mov edx, DWORD PTR [esp+28]
	mov ecx, ebx
25:
	movdqu XMMWORD PTR [edx], xmm0
	movzx ebp, BYTE PTR [eax]
	movd xmm1, ebp
	psrldq xmm0, 1
	pslldq xmm1, 15
	por xmm0, xmm1
	add eax, 1
	add edx, 16
	sub ecx, 1
	jne 25b
	mov ebp, DWORD PTR [esp+12]
	movdqu XMMWORD PTR [ebp], xmm0
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+28]
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks_ssse3}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov ebp, ebx
26:
	movzx eax, BYTE PTR [esi]
	movzx ecx, BYTE PTR [edx]
	xor eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 16
	sub ebp, 1
	jne 26b
	sub edi, ebx
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+1024]
	mov esi, DWORD PTR [eax+1028]
	mov edi, DWORD PTR [eax+1032]
	mov ebp, DWORD PTR [eax+1036]
	lea esp, [esp+1084]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1108]
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
	mov DWORD PTR [esp+1104], ecx
	lea esp, [esp+1108]
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

vg_aes_cfb8_encrypt:
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
	movzx eax, BYTE PTR [esi]
	movzx ecx, BYTE PTR [ebp+2048]
	xor eax, ecx
	mov BYTE PTR [esi], al
	mov ebx, DWORD PTR [esp+12]
	mov ecx, DWORD PTR [ebx+1]
	mov edx, DWORD PTR [ebx+5]
	mov edi, DWORD PTR [ebx+9]
	mov ebp, DWORD PTR [ebx+12]
	mov DWORD PTR [ebx], ecx
	mov DWORD PTR [ebx+4], edx
	mov DWORD PTR [ebx+8], edi
	mov DWORD PTR [ebx+11], ebp
	mov BYTE PTR [ebx+15], al
	add esi, 1
	mov eax, DWORD PTR [esp+20]
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

vg_aes_cfb8_decrypt:
	lea esp, [esp-1084]
	mov eax, DWORD PTR [esp+1088]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1092]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1096]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1100]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1104]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+1108]
	mov DWORD PTR [esp+24], eax
	mov eax, esp
	add eax, 32
	mov DWORD PTR [esp+28], eax
	mov eax, DWORD PTR [esp+28]
	mov DWORD PTR [eax+1024], ebx
	mov DWORD PTR [eax+1028], esi
	mov DWORD PTR [eax+1032], edi
	mov DWORD PTR [eax+1036], ebp
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	test edi, edi
	je 20f
22:
	mov ebx, 64
	cmp edi, 64
	jb 23f
	jmp 24f
23:
	mov ebx, edi
24:
	mov ebp, DWORD PTR [esp+12]
	movdqu xmm0, XMMWORD PTR [ebp]
	mov eax, esi
	mov edx, DWORD PTR [esp+28]
	mov ecx, ebx
25:
	movdqu XMMWORD PTR [edx], xmm0
	movzx ebp, BYTE PTR [eax]
	movd xmm1, ebp
	psrldq xmm0, 1
	pslldq xmm1, 15
	por xmm0, xmm1
	add eax, 1
	add edx, 16
	sub ecx, 1
	jne 25b
	mov ebp, DWORD PTR [esp+12]
	movdqu XMMWORD PTR [ebp], xmm0
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+28]
	mov ebp, DWORD PTR [esp+24]
	push ebp
	push ebx
	push edx
	push ecx
	push eax
	call {vg_aes_encrypt_blocks}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [esp+28]
	mov ebp, ebx
26:
	movzx eax, BYTE PTR [esi]
	movzx ecx, BYTE PTR [edx]
	xor eax, ecx
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 16
	sub ebp, 1
	jne 26b
	sub edi, ebx
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [esp+28]
	mov ebx, DWORD PTR [eax+1024]
	mov esi, DWORD PTR [eax+1028]
	mov edi, DWORD PTR [eax+1032]
	mov ebp, DWORD PTR [eax+1036]
	lea esp, [esp+1084]
	pxor xmm0, xmm0
	mov ecx, 0
	lea esp, [esp-1108]
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
	mov DWORD PTR [esp+1104], ecx
	lea esp, [esp+1108]
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
