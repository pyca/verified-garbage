// The functions of `src/internal/vg_aes_xts_encrypt_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_aesni:
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+2064], ebx
	mov DWORD PTR [eax+2068], esi
	mov DWORD PTR [eax+2072], edi
	mov DWORD PTR [eax+2076], ebp
	mov esi, DWORD PTR [esp+16]
	mov eax, DWORD PTR [esp+20]
	test eax, eax
	je 20f
	mov edx, DWORD PTR [esp+24]
	mov eax, 135
	movd xmm6, eax
	mov eax, 1
	movd xmm7, eax
	punpcklqdq xmm6, xmm7
	movdqu XMMWORD PTR [edx+368], xmm6
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+20]
	movdqu xmm7, XMMWORD PTR [ebp]
	cmp edi, 6
	jb 22f
24:
	movdqu xmm4, XMMWORD PTR [edx+368]
	pshufd xmm5, xmm7, 95
	psrld xmm5, 16
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edx+256], xmm7
	movdqa xmm6, xmm5
	psraw xmm6, 15
	paddw xmm5, xmm5
	pand xmm6, xmm4
	paddq xmm7, xmm7
	pxor xmm7, xmm6
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edx+272], xmm7
	movdqa xmm6, xmm5
	psraw xmm6, 15
	paddw xmm5, xmm5
	pand xmm6, xmm4
	paddq xmm7, xmm7
	pxor xmm7, xmm6
	movdqu xmm2, XMMWORD PTR [esi+32]
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edx+288], xmm7
	movdqa xmm6, xmm5
	psraw xmm6, 15
	paddw xmm5, xmm5
	pand xmm6, xmm4
	paddq xmm7, xmm7
	pxor xmm7, xmm6
	movdqu xmm3, XMMWORD PTR [esi+48]
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edx+304], xmm7
	movdqa xmm6, xmm5
	psraw xmm6, 15
	paddw xmm5, xmm5
	pand xmm6, xmm4
	paddq xmm7, xmm7
	pxor xmm7, xmm6
	movdqa xmm6, xmm5
	paddw xmm6, xmm6
	psraw xmm6, 15
	pand xmm6, xmm4
	movdqu XMMWORD PTR [edx+352], xmm6
	psraw xmm5, 15
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [esi+64]
	pxor xmm4, xmm7
	movdqu XMMWORD PTR [edx+320], xmm7
	paddq xmm7, xmm7
	pxor xmm7, xmm5
	movdqu xmm5, XMMWORD PTR [esi+80]
	pxor xmm5, xmm7
	movdqu XMMWORD PTR [edx+336], xmm7
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
	je 25f
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
	je 27f
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
	jmp 28f
27:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
28:
	jmp 26f
25:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
	aesenclast xmm1, xmm6
	aesenclast xmm2, xmm6
	aesenclast xmm3, xmm6
	aesenclast xmm4, xmm6
	aesenclast xmm5, xmm6
26:
	movdqu xmm6, XMMWORD PTR [edx+256]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm6, XMMWORD PTR [edx+272]
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [esi+16], xmm1
	movdqu xmm6, XMMWORD PTR [edx+288]
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [esi+32], xmm2
	movdqu xmm6, XMMWORD PTR [edx+304]
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [esi+48], xmm3
	movdqu xmm6, XMMWORD PTR [edx+320]
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [esi+64], xmm4
	movdqu xmm6, XMMWORD PTR [edx+336]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [esi+80], xmm5
	movdqu xmm6, XMMWORD PTR [edx+352]
	paddq xmm7, xmm7
	pxor xmm7, xmm6
	add esi, 96
	sub edi, 6
	cmp edi, 6
	jae 24b
	jmp 23f
22:
23:
	test edi, edi
	je 29f
211:
	movdqu xmm4, XMMWORD PTR [edx+368]
	pshufd xmm5, xmm7, 95
	psrld xmm5, 16
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edx+256], xmm7
	movdqa xmm6, xmm5
	psraw xmm6, 15
	paddw xmm5, xmm5
	pand xmm6, xmm4
	paddq xmm7, xmm7
	pxor xmm7, xmm6
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
	je 212f
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	aesenc xmm0, xmm6
	cmp ecx, 12
	je 214f
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	aesenc xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+224]
	aesenclast xmm0, xmm6
	jmp 215f
214:
	movdqu xmm6, XMMWORD PTR [eax+192]
	aesenclast xmm0, xmm6
215:
	jmp 213f
212:
	movdqu xmm6, XMMWORD PTR [eax+160]
	aesenclast xmm0, xmm6
213:
	movdqu xmm6, XMMWORD PTR [edx+256]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub edi, 1
	jne 211b
	jmp 210f
29:
210:
	movdqu XMMWORD PTR [ebp], xmm7
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
