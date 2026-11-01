// The functions of `src/scrypt.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_salsa20_8:
	mov eax, DWORD PTR [esp+4]
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [eax+16]
	movdqu xmm2, XMMWORD PTR [eax+32]
	movdqu xmm3, XMMWORD PTR [eax+48]
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	punpckldq xmm4, xmm1
	movdqa xmm5, xmm0
	punpckhdq xmm5, xmm1
	movdqa xmm6, xmm2
	punpckldq xmm6, xmm3
	movdqa xmm7, xmm2
	punpckhdq xmm7, xmm3
	movdqa xmm0, xmm4
	punpcklqdq xmm0, xmm6
	movdqa xmm1, xmm4
	punpckhqdq xmm1, xmm6
	movdqa xmm2, xmm5
	punpcklqdq xmm2, xmm7
	movdqa xmm3, xmm5
	punpckhqdq xmm3, xmm7
	pshufd xmm4, xmm3, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm1, 147
	movdqa xmm1, xmm4
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	movdqa xmm4, xmm0
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 57
	movdqa xmm4, xmm0
	paddd xmm4, xmm1
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqa xmm4, xmm3
	paddd xmm4, xmm0
	movdqa xmm5, xmm4
	pslld xmm4, 9
	psrld xmm5, 23
	pxor xmm2, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm2
	paddd xmm4, xmm3
	movdqa xmm5, xmm4
	pslld xmm4, 13
	psrld xmm5, 19
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqa xmm4, xmm1
	paddd xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 18
	psrld xmm5, 14
	pxor xmm0, xmm4
	pxor xmm0, xmm5
	pshufd xmm1, xmm1, 57
	pshufd xmm2, xmm2, 78
	pshufd xmm3, xmm3, 147
	pshufd xmm4, xmm1, 147
	pshufd xmm1, xmm3, 57
	pshufd xmm2, xmm2, 78
	movdqa xmm3, xmm0
	punpckldq xmm3, xmm1
	movdqa xmm5, xmm0
	punpckhdq xmm5, xmm1
	movdqa xmm6, xmm2
	punpckldq xmm6, xmm4
	movdqa xmm7, xmm2
	punpckhdq xmm7, xmm4
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm6
	movdqa xmm1, xmm3
	punpckhqdq xmm1, xmm6
	movdqa xmm2, xmm5
	punpcklqdq xmm2, xmm7
	movdqa xmm4, xmm5
	punpckhqdq xmm4, xmm7
	pshufd xmm1, xmm1, 147
	pshufd xmm2, xmm2, 78
	pshufd xmm4, xmm4, 57
	movdqu xmm3, XMMWORD PTR [eax]
	movdqu xmm5, XMMWORD PTR [eax+16]
	movdqu xmm6, XMMWORD PTR [eax+32]
	movdqu xmm7, XMMWORD PTR [eax+48]
	paddd xmm0, xmm3
	paddd xmm1, xmm5
	paddd xmm2, xmm6
	paddd xmm4, xmm7
	movdqu XMMWORD PTR [eax], xmm0
	movdqu XMMWORD PTR [eax+16], xmm1
	movdqu XMMWORD PTR [eax+32], xmm2
	movdqu XMMWORD PTR [eax+48], xmm4
	ret
	.p2align 6

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

vg_scrypt_romix:
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+128], ebx
	mov DWORD PTR [eax+132], esi
	mov DWORD PTR [eax+136], edi
	mov DWORD PTR [eax+140], ebp
	mov eax, DWORD PTR [esp+8]
	mov ecx, 1
	mov edx, DWORD PTR [esp+16]
	add edx, edx
20:
	add eax, eax
	add ecx, ecx
	cmp eax, edx
	jne 20b
	shr ecx, 1
	mov ebp, ecx
	mov ebx, ecx
	mov esi, DWORD PTR [esp+12]
21:
	mov eax, DWORD PTR [esp+8]
	mov ecx, 8
	mul ecx
	mov edx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, esi
22:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [ecx], xmm0
	add eax, 16
	add ecx, 16
	sub edx, 1
	jne 22b
	mov eax, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push eax
	push ecx
	push edx
	push ecx
	push esi
	call {vg_scrypt_blockmix}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [esp+8]
	mov ecx, 128
	mul ecx
	add esi, eax
	sub ebx, 1
	jne 21b
	mov ebx, ebp
23:
	mov eax, DWORD PTR [esp+8]
	mov ecx, 128
	mul ecx
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	add eax, ecx
	sub eax, 64
	mov eax, DWORD PTR [eax]
	mov ecx, ebp
	sub ecx, 1
	and eax, ecx
	mul edi
	mov ecx, DWORD PTR [esp+12]
	add ecx, eax
	mov eax, DWORD PTR [esp+4]
	mov edx, DWORD PTR [esp+20]
	add edx, 192
	shr edi, 4
24:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ecx]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edx], xmm0
	add eax, 16
	add ecx, 16
	add edx, 16
	sub edi, 1
	jne 24b
	mov esi, DWORD PTR [esp+20]
	add esi, 192
	mov eax, DWORD PTR [esp+20]
	mov ecx, DWORD PTR [esp+8]
	mov edx, DWORD PTR [esp+4]
	push eax
	push ecx
	push edx
	push ecx
	push esi
	call {vg_scrypt_blockmix}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	sub ebx, 1
	jne 23b
	mov eax, DWORD PTR [esp+20]
	mov ebx, DWORD PTR [eax+128]
	mov esi, DWORD PTR [eax+132]
	mov edi, DWORD PTR [eax+136]
	mov ebp, DWORD PTR [eax+140]
	ret
	.p2align 6

vg_scrypt:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch}
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
20:
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	add eax, 2
	mov DWORD PTR [esp+20], eax
	call {vg_scrypt_romix}
	mov ecx, DWORD PTR [esp+56]
	ror ecx, 25
	mov eax, DWORD PTR [esp+32]
	add eax, ecx
	mov edx, DWORD PTR [esp+64]
	ror edx, 25
	add edx, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
	cmp eax, edx
	jne 20b
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6

vg_scrypt_shani:
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	push eax
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+48]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+52]
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
20:
	mov eax, DWORD PTR [esp+32]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+56]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+68]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+72]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+56]
	add eax, 2
	mov DWORD PTR [esp+20], eax
	call {vg_scrypt_romix}
	mov ecx, DWORD PTR [esp+56]
	ror ecx, 25
	mov eax, DWORD PTR [esp+32]
	add eax, ecx
	mov edx, DWORD PTR [esp+64]
	ror edx, 25
	add edx, DWORD PTR [esp+60]
	mov DWORD PTR [esp+32], eax
	cmp eax, edx
	jne 20b
	mov eax, DWORD PTR [esp+40]
	mov DWORD PTR [esp], eax
	mov eax, DWORD PTR [esp+44]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+60]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+64]
	ror eax, 25
	mov DWORD PTR [esp+12], eax
	mov eax, 1
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+84]
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+76]
	mov DWORD PTR [esp+28], eax
	call {vg_pbkdf2_hmac_sha256_scratch_shani}
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	pop eax
	ret
	.p2align 6
