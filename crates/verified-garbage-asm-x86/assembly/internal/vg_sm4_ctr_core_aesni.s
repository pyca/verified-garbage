// The functions of `src/internal/vg_sm4_ctr_core_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr_core_aesni:
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov eax, DWORD PTR [edi+720]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+716]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [edi+712]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+712], eax
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
	mov ecx, 0
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	mov DWORD PTR [esp+60], ecx
	mov DWORD PTR [esp+64], ecx
	mov DWORD PTR [esp+68], ecx
	mov DWORD PTR [esp+72], ecx
	mov DWORD PTR [esp+76], ecx
	mov DWORD PTR [esp+80], ecx
	mov DWORD PTR [esp+84], ecx
	mov DWORD PTR [esp+88], ecx
	mov DWORD PTR [esp+92], ecx
	mov DWORD PTR [esp+96], ecx
	mov DWORD PTR [esp+100], ecx
	mov DWORD PTR [esp+104], ecx
	mov DWORD PTR [esp+108], ecx
	mov DWORD PTR [esp+112], ecx
	mov DWORD PTR [esp+116], ecx
	mov DWORD PTR [esp+120], ecx
	mov DWORD PTR [esp+124], ecx
	mov DWORD PTR [esp+128], ecx
	mov DWORD PTR [esp+132], ecx
	mov DWORD PTR [esp+136], ecx
	mov DWORD PTR [esp+140], ecx
	mov DWORD PTR [esp+144], ecx
	mov DWORD PTR [esp+148], ecx
	mov DWORD PTR [esp+152], ecx
	mov DWORD PTR [esp+156], ecx
	mov DWORD PTR [esp+160], ecx
	mov DWORD PTR [esp+164], ecx
	mov DWORD PTR [esp+168], ecx
	mov DWORD PTR [esp+172], ecx
	mov DWORD PTR [esp+176], ecx
	mov DWORD PTR [esp+180], ecx
	mov DWORD PTR [esp+184], ecx
	mov DWORD PTR [esp+188], ecx
	mov DWORD PTR [esp+192], ecx
	mov DWORD PTR [esp+196], ecx
	mov DWORD PTR [esp+200], ecx
	mov DWORD PTR [esp+204], ecx
	mov DWORD PTR [esp+208], ecx
	mov DWORD PTR [esp+212], ecx
	mov DWORD PTR [esp+216], ecx
	mov DWORD PTR [esp+220], ecx
	mov DWORD PTR [esp+224], ecx
	mov DWORD PTR [esp+228], ecx
	mov DWORD PTR [esp+232], ecx
	mov DWORD PTR [esp+236], ecx
	mov DWORD PTR [esp+240], ecx
	mov DWORD PTR [esp+244], ecx
	mov DWORD PTR [esp+248], ecx
	mov DWORD PTR [esp+252], ecx
	mov DWORD PTR [esp+256], ecx
	mov DWORD PTR [esp+260], ecx
	mov DWORD PTR [esp+264], ecx
	mov DWORD PTR [esp+268], ecx
	mov DWORD PTR [esp+272], ecx
	mov DWORD PTR [esp+276], ecx
	mov DWORD PTR [esp+280], ecx
	mov DWORD PTR [esp+284], ecx
	mov DWORD PTR [esp+288], ecx
	mov DWORD PTR [esp+292], ecx
	mov DWORD PTR [esp+296], ecx
	mov DWORD PTR [esp+300], ecx
	mov DWORD PTR [esp+304], ecx
	mov DWORD PTR [esp+308], ecx
	mov DWORD PTR [esp+312], ecx
	mov DWORD PTR [esp+316], ecx
	mov DWORD PTR [esp+320], ecx
	mov DWORD PTR [esp+324], ecx
	mov DWORD PTR [esp+328], ecx
	mov DWORD PTR [esp+332], ecx
	mov DWORD PTR [esp+336], ecx
	mov DWORD PTR [esp+340], ecx
	mov DWORD PTR [esp+344], ecx
	mov DWORD PTR [esp+348], ecx
	mov DWORD PTR [esp+352], ecx
	mov DWORD PTR [esp+356], ecx
	mov DWORD PTR [esp+360], ecx
	mov DWORD PTR [esp+364], ecx
	mov DWORD PTR [esp+368], ecx
	mov DWORD PTR [esp+372], ecx
	mov DWORD PTR [esp+376], ecx
	mov DWORD PTR [esp+380], ecx
	mov DWORD PTR [esp+384], ecx
	mov DWORD PTR [esp+388], ecx
	mov DWORD PTR [esp+392], ecx
	mov DWORD PTR [esp+396], ecx
	mov DWORD PTR [esp+400], ecx
	mov DWORD PTR [esp+404], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	mov DWORD PTR [esp+420], ecx
	mov DWORD PTR [esp+424], ecx
	mov DWORD PTR [esp+428], ecx
	mov DWORD PTR [esp+432], ecx
	mov DWORD PTR [esp+436], ecx
	mov DWORD PTR [esp+440], ecx
	mov DWORD PTR [esp+444], ecx
	mov DWORD PTR [esp+448], ecx
	mov DWORD PTR [esp+452], ecx
	mov DWORD PTR [esp+456], ecx
	mov DWORD PTR [esp+460], ecx
	mov DWORD PTR [esp+464], ecx
	mov DWORD PTR [esp+468], ecx
	mov DWORD PTR [esp+472], ecx
	mov DWORD PTR [esp+476], ecx
	mov DWORD PTR [esp+480], ecx
	mov DWORD PTR [esp+484], ecx
	mov DWORD PTR [esp+488], ecx
	mov DWORD PTR [esp+492], ecx
	mov DWORD PTR [esp+496], ecx
	mov DWORD PTR [esp+500], ecx
	mov DWORD PTR [esp+504], ecx
	mov DWORD PTR [esp+508], ecx
	mov DWORD PTR [esp+512], ecx
	mov DWORD PTR [esp+516], ecx
	mov DWORD PTR [esp+520], ecx
	mov DWORD PTR [esp+524], ecx
	mov DWORD PTR [esp+528], ecx
	mov DWORD PTR [esp+532], ecx
	mov DWORD PTR [esp+536], ecx
	mov DWORD PTR [esp+540], ecx
	mov DWORD PTR [esp+544], ecx
	mov DWORD PTR [esp+548], ecx
	mov DWORD PTR [esp+552], ecx
	mov DWORD PTR [esp+556], ecx
	mov DWORD PTR [esp+560], ecx
	mov DWORD PTR [esp+564], ecx
	mov DWORD PTR [esp+568], ecx
	mov DWORD PTR [esp+572], ecx
	mov DWORD PTR [esp+576], ecx
	mov DWORD PTR [esp+580], ecx
	mov DWORD PTR [esp+584], ecx
	mov DWORD PTR [esp+588], ecx
	mov DWORD PTR [esp+592], ecx
	mov DWORD PTR [esp+596], ecx
	mov DWORD PTR [esp+600], ecx
	mov DWORD PTR [esp+604], ecx
	mov DWORD PTR [esp+608], ecx
	mov DWORD PTR [esp+612], ecx
	mov DWORD PTR [esp+616], ecx
	mov DWORD PTR [esp+620], ecx
	mov DWORD PTR [esp+624], ecx
	mov DWORD PTR [esp+628], ecx
	mov DWORD PTR [esp+632], ecx
	mov DWORD PTR [esp+636], ecx
	mov DWORD PTR [esp+640], ecx
	mov DWORD PTR [esp+644], ecx
	mov DWORD PTR [esp+648], ecx
	mov DWORD PTR [esp+652], ecx
	mov DWORD PTR [esp+656], ecx
	mov DWORD PTR [esp+660], ecx
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	mov DWORD PTR [esp+672], ecx
	mov DWORD PTR [esp+676], ecx
	mov DWORD PTR [esp+680], ecx
	mov DWORD PTR [esp+684], ecx
	mov DWORD PTR [esp+688], ecx
	mov DWORD PTR [esp+692], ecx
	mov DWORD PTR [esp+696], ecx
	mov DWORD PTR [esp+700], ecx
	mov DWORD PTR [esp+704], ecx
	mov DWORD PTR [esp+708], ecx
	mov DWORD PTR [esp+712], ecx
	mov DWORD PTR [esp+716], ecx
	mov DWORD PTR [esp+720], ecx
	mov DWORD PTR [esp+724], ecx
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	mov DWORD PTR [esp+736], ecx
	mov DWORD PTR [esp+740], ecx
	mov DWORD PTR [esp+744], ecx
	mov DWORD PTR [esp+748], ecx
	lea esp, [esp+752]
	ret
	.p2align 6
