// The functions of `src/internal/vg_sm4_expand_key_core_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key_core_aesni:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SM4_KEY_AESNI}
	pop ecx
	mov edx, DWORD PTR [esp+8]
	movdqu xmm6, XMMWORD PTR [eax+256]
	movdqu XMMWORD PTR [edx], xmm6
	movdqu xmm6, XMMWORD PTR [eax+272]
	movdqu XMMWORD PTR [edx+16], xmm6
	movdqu xmm6, XMMWORD PTR [eax+288]
	movdqu XMMWORD PTR [edx+32], xmm6
	movdqu xmm6, XMMWORD PTR [eax+304]
	movdqu XMMWORD PTR [edx+48], xmm6
	movdqu xmm6, XMMWORD PTR [eax+320]
	movdqu XMMWORD PTR [edx+64], xmm6
	movdqu xmm6, XMMWORD PTR [eax+336]
	movdqu XMMWORD PTR [edx+80], xmm6
	movdqu xmm6, XMMWORD PTR [eax+352]
	movdqu XMMWORD PTR [edx+96], xmm6
	movdqu xmm6, XMMWORD PTR [eax+368]
	movdqu XMMWORD PTR [edx+112], xmm6
	mov ecx, DWORD PTR [esp+4]
	movdqu xmm7, XMMWORD PTR [eax]
	movdqu xmm4, XMMWORD PTR [ecx]
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+16]
	pshufb xmm6, xmm4
	movdqu xmm4, XMMWORD PTR [eax+32]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [eax+224]
	pxor xmm6, xmm5
	pshufd xmm0, xmm6, 0
	pshufd xmm1, xmm6, 85
	pshufd xmm2, xmm6, 170
	pshufd xmm3, xmm6, 255
	mov ecx, 8
20:
	movdqu xmm4, XMMWORD PTR [edx]
	pxor xmm4, xmm1
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edx]
	pshufd xmm4, xmm4, 1
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	pxor xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edx]
	pshufd xmm4, xmm4, 2
	pxor xmm4, xmm3
	pxor xmm4, xmm0
	pxor xmm4, xmm1
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edx]
	pshufd xmm4, xmm4, 3
	pxor xmm4, xmm0
	pxor xmm4, xmm1
	pxor xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [eax+240]
	pshufb xmm4, xmm6
	aesenclast xmm4, xmm7
	movdqa xmm5, xmm4
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm4, xmm7
	movdqu xmm6, XMMWORD PTR [eax+96]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+112]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+128]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+144]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+160]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+176]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	pshufd xmm4, xmm4, 57
	pshufd xmm5, xmm5, 57
	movdqu xmm6, XMMWORD PTR [eax+192]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [eax+208]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm6, xmm0
	punpcklqdq xmm6, xmm1
	pshufd xmm6, xmm6, 136
	movdqa xmm5, xmm2
	punpcklqdq xmm5, xmm3
	pshufd xmm5, xmm5, 136
	punpcklqdq xmm6, xmm5
	movdqa xmm5, xmm6
	psrld xmm5, 4
	pand xmm5, xmm7
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [eax+48]
	pshufb xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+64]
	pshufb xmm6, xmm5
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [eax+80]
	pshufb xmm4, xmm6
	movdqu XMMWORD PTR [edx], xmm4
	add edx, 16
	sub ecx, 1
	jne 20b
	ret
	.p2align 6
