// The functions of `src/internal/vg_sm4_ctr32_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32_aesni:
	lea esp, [esp-752]
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+760]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+764]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+768]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+688], ebx
	mov DWORD PTR [eax+692], esi
	mov DWORD PTR [eax+696], edi
	mov DWORD PTR [eax+700], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+724], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
	movdqu xmm7, XMMWORD PTR [ebx]
20:
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ebx+224]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	pshufd xmm3, xmm2, 0
	movdqu XMMWORD PTR [esi], xmm3
	pshufd xmm3, xmm2, 85
	movdqu XMMWORD PTR [esi+16], xmm3
	pshufd xmm3, xmm2, 170
	movdqu XMMWORD PTR [esi+32], xmm3
	pshufd xmm3, xmm2, 255
	movdqu XMMWORD PTR [esi+48], xmm3
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+708], eax
	test eax, eax
	mov eax, DWORD PTR [edi+708]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+672], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+676], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+680], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+684], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
24:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu xmm1, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+48], xmm1
	movdqu xmm2, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [edi+32]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm1, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+672]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+676]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+680]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+684]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+708]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
28:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu xmm1, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+48], xmm1
	movdqu xmm2, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [edi+32]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm1, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	add esi, 64
	sub eax, 1
	jne 28b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+708]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+724]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+724], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+128]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+640]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+656]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+672]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqa xmm2, xmm3
	pxor xmm2, xmm4
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu xmm0, XMMWORD PTR [esi]
	pxor xmm0, xmm2
212:
	movdqu xmm2, XMMWORD PTR [esi+16]
	movdqu xmm6, XMMWORD PTR [edi+64]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+32]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu xmm1, XMMWORD PTR [esi+32]
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+48], xmm1
	movdqu xmm2, XMMWORD PTR [esi+48]
	movdqu xmm6, XMMWORD PTR [edi+32]
	pxor xmm2, xmm6
	pxor xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm0, xmm6
	aesenclast xmm0, xmm7
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqa xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	pxor xmm3, xmm4
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm4, xmm3
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm1, XMMWORD PTR [esi+64]
	movdqu xmm6, XMMWORD PTR [edi+48]
	pxor xmm1, xmm6
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm2
	movdqa xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm4
	pxor xmm5, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	pxor xmm0, xmm3
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+80], xmm1
	add esi, 64
	sub eax, 1
	jne 212b
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+48]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+32]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+160]
	pshufb xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm4, xmm0
	punpcklqdq xmm0, xmm1
	pshufd xmm0, xmm0, 216
	punpckhqdq xmm4, xmm1
	pshufd xmm4, xmm4, 216
	movdqa xmm5, xmm2
	punpcklqdq xmm2, xmm3
	pshufd xmm2, xmm2, 216
	punpckhqdq xmm5, xmm3
	pshufd xmm5, xmm5, 216
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm3, xmm2
	movdqa xmm1, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm1, xmm5
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu XMMWORD PTR [edi+656], xmm4
	movdqu XMMWORD PTR [edi+672], xmm1
	mov esi, DWORD PTR [edi+704]
	mov ebp, DWORD PTR [edi+708]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+704], esi
	mov DWORD PTR [edi+708], ebp
	jne 211b
	jmp 210f
29:
210:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+688]
	mov esi, DWORD PTR [edi+692]
	mov ebp, DWORD PTR [edi+700]
	mov edi, DWORD PTR [edi+696]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+24], xmm0
	movdqu XMMWORD PTR [esp+40], xmm0
	movdqu XMMWORD PTR [esp+56], xmm0
	movdqu XMMWORD PTR [esp+72], xmm0
	movdqu XMMWORD PTR [esp+88], xmm0
	movdqu XMMWORD PTR [esp+104], xmm0
	movdqu XMMWORD PTR [esp+120], xmm0
	movdqu XMMWORD PTR [esp+136], xmm0
	movdqu XMMWORD PTR [esp+152], xmm0
	movdqu XMMWORD PTR [esp+168], xmm0
	movdqu XMMWORD PTR [esp+184], xmm0
	movdqu XMMWORD PTR [esp+200], xmm0
	movdqu XMMWORD PTR [esp+216], xmm0
	movdqu XMMWORD PTR [esp+232], xmm0
	movdqu XMMWORD PTR [esp+248], xmm0
	movdqu XMMWORD PTR [esp+264], xmm0
	movdqu XMMWORD PTR [esp+280], xmm0
	movdqu XMMWORD PTR [esp+296], xmm0
	movdqu XMMWORD PTR [esp+312], xmm0
	movdqu XMMWORD PTR [esp+328], xmm0
	movdqu XMMWORD PTR [esp+344], xmm0
	movdqu XMMWORD PTR [esp+360], xmm0
	movdqu XMMWORD PTR [esp+376], xmm0
	movdqu XMMWORD PTR [esp+392], xmm0
	movdqu XMMWORD PTR [esp+408], xmm0
	movdqu XMMWORD PTR [esp+424], xmm0
	movdqu XMMWORD PTR [esp+440], xmm0
	movdqu XMMWORD PTR [esp+456], xmm0
	movdqu XMMWORD PTR [esp+472], xmm0
	movdqu XMMWORD PTR [esp+488], xmm0
	movdqu XMMWORD PTR [esp+504], xmm0
	movdqu XMMWORD PTR [esp+520], xmm0
	movdqu XMMWORD PTR [esp+536], xmm0
	movdqu XMMWORD PTR [esp+552], xmm0
	movdqu XMMWORD PTR [esp+568], xmm0
	movdqu XMMWORD PTR [esp+584], xmm0
	movdqu XMMWORD PTR [esp+600], xmm0
	movdqu XMMWORD PTR [esp+616], xmm0
	movdqu XMMWORD PTR [esp+632], xmm0
	movdqu XMMWORD PTR [esp+648], xmm0
	movdqu XMMWORD PTR [esp+664], xmm0
	movdqu XMMWORD PTR [esp+680], xmm0
	movdqu XMMWORD PTR [esp+696], xmm0
	movdqu XMMWORD PTR [esp+712], xmm0
	movdqu XMMWORD PTR [esp+728], xmm0
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	lea esp, [esp+752]
	ret
	.p2align 6
