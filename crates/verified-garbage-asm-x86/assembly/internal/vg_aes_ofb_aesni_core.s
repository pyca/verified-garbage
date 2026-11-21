// The functions of `src/internal/vg_aes_ofb_aesni_core.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ofb_aesni_core:
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
	ret
	.p2align 6
