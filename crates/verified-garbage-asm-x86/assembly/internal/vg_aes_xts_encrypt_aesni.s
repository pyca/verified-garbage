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
	mov esi, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+20]
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	mov eax, 134
	movd xmm7, eax
	movdqa xmm5, xmm6
	psrld xmm5, 31
	pxor xmm7, xmm5
	movdqu xmm0, XMMWORD PTR [ebx]
22:
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [esi], xmm1
	pshufd xmm2, xmm0, 147
	psrld xmm2, 31
	paddd xmm2, xmm6
	pandn xmm2, xmm7
	paddd xmm0, xmm0
	pxor xmm0, xmm2
	add esi, 16
	sub edi, 1
	jne 22b
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+20]
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
	mov esi, DWORD PTR [esp+16]
	mov ebx, DWORD PTR [esp+12]
	mov edi, DWORD PTR [esp+20]
	mov eax, -1
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	mov eax, 134
	movd xmm7, eax
	movdqa xmm5, xmm6
	psrld xmm5, 31
	pxor xmm7, xmm5
	movdqu xmm0, XMMWORD PTR [ebx]
23:
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [esi], xmm1
	pshufd xmm2, xmm0, 147
	psrld xmm2, 31
	paddd xmm2, xmm6
	pandn xmm2, xmm7
	paddd xmm0, xmm0
	pxor xmm0, xmm2
	add esi, 16
	sub edi, 1
	jne 23b
	movdqu XMMWORD PTR [ebx], xmm0
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
