// The functions of `src/internal/vg_aes_ctr32_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov ebp, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+12]
	mov esi, DWORD PTR [esp+16]
	mov edi, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [edx+12]
	bswap ebx
	movdqu xmm7, XMMWORD PTR [edx]
	pslldq xmm7, 4
	psrldq xmm7, 4
	movdqu XMMWORD PTR [ebp+16], xmm7
	cmp edi, 6
	jb 20f
22:
	movdqu xmm7, XMMWORD PTR [ebp+16]
	mov eax, ebx
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm7
	add ebx, 1
	mov eax, ebx
	bswap eax
	movd xmm1, eax
	pslldq xmm1, 12
	por xmm1, xmm7
	add ebx, 1
	mov eax, ebx
	bswap eax
	movd xmm2, eax
	pslldq xmm2, 12
	por xmm2, xmm7
	add ebx, 1
	mov eax, ebx
	bswap eax
	movd xmm3, eax
	pslldq xmm3, 12
	por xmm3, xmm7
	add ebx, 1
	mov eax, ebx
	bswap eax
	movd xmm4, eax
	pslldq xmm4, 12
	por xmm4, xmm7
	add ebx, 1
	mov eax, ebx
	bswap eax
	movd xmm5, eax
	pslldq xmm5, 12
	por xmm5, xmm7
	add ebx, 1
	mov eax, DWORD PTR [esp+4]
	movdqu xmm6, XMMWORD PTR [eax]
	pxor xmm0, xmm6
	pxor xmm1, xmm6
	pxor xmm2, xmm6
	pxor xmm3, xmm6
	pxor xmm4, xmm6
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+16]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+32]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+48]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+96]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+128]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 10
	je 23f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	cmp ecx, 12
	je 25f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	aesenc xmm1, xmm6
	aesenc xmm2, xmm6
	aesenc xmm3, xmm6
	aesenc xmm4, xmm6
	aesenc xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
	jmp 26f
25:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
26:
	jmp 24f
23:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
24:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm7, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm7, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm7, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm7, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm7, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [esi+80], xmm5
	add esi, 96
	sub edi, 6
	cmp edi, 6
	jae 22b
	jmp 21f
20:
21:
	test edi, edi
	je 27f
29:
	movdqu xmm7, XMMWORD PTR [ebp+16]
	mov eax, ebx
	bswap eax
	movd xmm0, eax
	pslldq xmm0, 12
	por xmm0, xmm7
	add ebx, 1
	mov eax, DWORD PTR [esp+4]
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
	je 210f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 212f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 213f
212:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
213:
	jmp 211f
210:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
211:
	movdqu xmm7, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub edi, 1
	jne 29b
	jmp 28f
27:
28:
	mov eax, ebx
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov ebx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+4]
	mov edi, DWORD PTR [ebp+8]
	mov ebp, DWORD PTR [ebp+12]
	ret
	.p2align 6
