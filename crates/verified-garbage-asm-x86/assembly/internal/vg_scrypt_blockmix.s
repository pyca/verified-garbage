// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+64], ebx
	mov DWORD PTR [eax+68], esi
	mov DWORD PTR [eax+72], edi
	mov DWORD PTR [eax+76], ebp
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esp+8]
	mov ecx, 64
	mul ecx
	mov edi, esi
	add edi, eax
	mov ebp, ebx
	add ebp, eax
	add ebp, eax
	sub ebp, 64
20:
	movdqu xmm0, XMMWORD PTR [ebp]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi], xmm0
	movdqu xmm0, XMMWORD PTR [ebp+16]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi+16], xmm0
	movdqu xmm0, XMMWORD PTR [ebp+32]
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi+32], xmm0
	movdqu xmm0, XMMWORD PTR [ebp+48]
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [esi+48], xmm0
	mov eax, DWORD PTR [esp+20]
	push eax
	push esi
	call {vg_salsa20_8}
	pop eax
	pop eax
	add ebx, 64
	movdqu xmm0, XMMWORD PTR [esi]
	movdqu xmm1, XMMWORD PTR [ebx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi], xmm0
	movdqu xmm0, XMMWORD PTR [esi+16]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [esi+32]
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [esi+48]
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	mov eax, DWORD PTR [esp+20]
	push eax
	push edi
	call {vg_salsa20_8}
	pop eax
	pop eax
	mov ebp, edi
	add ebx, 64
	add esi, 64
	add edi, 64
	mov eax, DWORD PTR [esp+8]
	mov ecx, 64
	mul ecx
	mov ecx, DWORD PTR [esp+12]
	add eax, ecx
	cmp esi, eax
	jne 20b
	mov eax, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [eax+64]
	mov esi, DWORD PTR [eax+68]
	mov edi, DWORD PTR [eax+72]
	mov ebp, DWORD PTR [eax+76]
	ret
	.p2align 6
