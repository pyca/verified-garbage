// The functions of `src/camellia.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key_aesni:
	lea esp, [esp-416]
	mov eax, DWORD PTR [esp+420]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+424]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+428]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI}
	pop ecx
	mov edx, eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+368], ebx
	mov DWORD PTR [eax+372], esi
	mov DWORD PTR [eax+376], edi
	mov DWORD PTR [eax+380], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 20f
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 24
	je 22f
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+316], eax
	jmp 23f
22:
	mov eax, DWORD PTR [ecx+16]
	xor eax, -1
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [ecx+20]
	xor eax, -1
	mov DWORD PTR [edi+316], eax
23:
	jmp 21f
20:
	mov eax, 0
	mov DWORD PTR [edi+304], eax
	mov DWORD PTR [edi+308], eax
	mov DWORD PTR [edi+312], eax
	mov DWORD PTR [edi+316], eax
21:
	mov ebx, edx
	mov esi, edi
	movdqu xmm0, XMMWORD PTR [ebx+512]
	movdqu XMMWORD PTR [edi], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+528]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+544]
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+560]
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+576]
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+592]
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm0, XMMWORD PTR [edi+288]
	movdqu xmm1, XMMWORD PTR [edi+304]
	pxor xmm0, xmm1
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm5, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm5
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm2, xmm4
	pand xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm2
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [esi]
	pxor xmm3, xmm5
	pxor xmm2, xmm2
	pshufd xmm1, xmm3, 78
	punpcklqdq xmm1, xmm2
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm2
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	movq xmm5, QWORD PTR [esi+48]
	pxor xmm0, xmm5
	aesenclast xmm2, xmm7
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+208]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqa xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+272]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	pshufd xmm2, xmm1, 78
	pxor xmm2, xmm1
	movq xmm5, QWORD PTR [esi+56]
	pxor xmm1, xmm5
	aesenclast xmm2, xmm7
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+208]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqa xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pshufb xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+272]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pshufb xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	pshufd xmm3, xmm1, 78
	pxor xmm3, xmm1
	punpcklqdq xmm2, xmm3
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm3, xmm5
	pand xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm5
	movdqu xmm0, XMMWORD PTR [edi+288]
	pxor xmm0, xmm4
	add esi, 32
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm5, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm5
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm2, xmm4
	pand xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm2
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [esi]
	pxor xmm3, xmm5
	pxor xmm2, xmm2
	pshufd xmm1, xmm3, 78
	punpcklqdq xmm1, xmm2
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm2
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	movq xmm5, QWORD PTR [esi+48]
	pxor xmm0, xmm5
	aesenclast xmm2, xmm7
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+208]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqa xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+272]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	pshufd xmm2, xmm1, 78
	pxor xmm2, xmm1
	movq xmm5, QWORD PTR [esi+56]
	pxor xmm1, xmm5
	aesenclast xmm2, xmm7
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+208]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqa xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pshufb xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+272]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pshufb xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	pshufd xmm3, xmm1, 78
	pxor xmm3, xmm1
	punpcklqdq xmm2, xmm3
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm3, xmm5
	pand xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm5
	movdqu XMMWORD PTR [edi+336], xmm4
	movdqu xmm0, XMMWORD PTR [edi+304]
	pxor xmm0, xmm4
	add esi, 32
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm5, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm5
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm2, xmm4
	pand xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm2
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [esi]
	pxor xmm3, xmm5
	pxor xmm2, xmm2
	pshufd xmm1, xmm3, 78
	punpcklqdq xmm1, xmm2
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm2
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	movq xmm5, QWORD PTR [esi+48]
	pxor xmm0, xmm5
	aesenclast xmm2, xmm7
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+208]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqa xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+272]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	pshufd xmm2, xmm1, 78
	pxor xmm2, xmm1
	movq xmm5, QWORD PTR [esi+56]
	pxor xmm1, xmm5
	aesenclast xmm2, xmm7
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+208]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqa xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	pshufb xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+272]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+368]
	pshufb xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	pshufb xmm6, xmm2
	pxor xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm6
	pxor xmm0, xmm5
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	pshufd xmm3, xmm1, 78
	pxor xmm3, xmm1
	punpcklqdq xmm2, xmm3
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm3, xmm5
	pand xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+144]
	pshufb xmm6, xmm2
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pshufb xmm6, xmm5
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm5
	movdqu XMMWORD PTR [edi+352], xmm4
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	bswap eax
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	bswap eax
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	bswap eax
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	bswap eax
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+336]
	bswap eax
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	bswap eax
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	bswap eax
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	bswap eax
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+352]
	bswap eax
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	bswap eax
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	bswap eax
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	bswap eax
	mov DWORD PTR [edi+364], eax
	mov edx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 24f
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+352]
	bswap eax
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+356]
	bswap eax
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+360]
	bswap eax
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+364]
	bswap eax
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+124], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+128], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+132], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+136], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+140], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+144], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+148], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+152], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+156], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+160], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+164], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+168], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+172], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+176], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+180], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+184], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+188], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+192], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+196], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+200], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+204], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+208], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+212], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+216], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+220], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+224], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+228], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+232], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+236], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+240], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+244], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+248], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+252], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+256], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+260], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+264], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+268], eax
	jmp 25f
24:
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+336]
	bswap eax
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+340]
	bswap eax
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+344]
	bswap eax
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+348]
	bswap eax
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+124], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+128], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+132], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+136], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+140], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+144], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+148], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+152], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+156], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+160], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+164], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+168], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+172], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+176], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+180], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+184], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+188], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+192], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+196], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+200], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+204], eax
25:
	mov ebx, DWORD PTR [edi+368]
	mov esi, DWORD PTR [edi+372]
	mov ebp, DWORD PTR [edi+380]
	mov edi, DWORD PTR [edi+376]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	lea esp, [esp+416]
	lea esp, [esp-420]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+408], ecx
	mov DWORD PTR [esp+412], ecx
	mov DWORD PTR [esp+416], ecx
	lea esp, [esp+420]
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

vg_camellia_expand_key:
	lea esp, [esp-1504]
	mov eax, DWORD PTR [esp+1508]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1512]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1516]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_SSE2}
	pop ecx
	mov edx, eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+368], ebx
	mov DWORD PTR [eax+372], esi
	mov DWORD PTR [eax+376], edi
	mov DWORD PTR [eax+380], ebp
	mov edi, eax
	mov ecx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [ecx]
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [ecx+4]
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [ecx+8]
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [ecx+12]
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 20f
	mov eax, DWORD PTR [ecx+16]
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [ecx+20]
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [esp+8]
	cmp eax, 24
	je 22f
	mov eax, DWORD PTR [ecx+24]
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [ecx+28]
	mov DWORD PTR [edi+316], eax
	jmp 23f
22:
	mov eax, DWORD PTR [ecx+16]
	xor eax, -1
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [ecx+20]
	xor eax, -1
	mov DWORD PTR [edi+316], eax
23:
	jmp 21f
20:
	mov eax, 0
	mov DWORD PTR [edi+304], eax
	mov DWORD PTR [edi+308], eax
	mov DWORD PTR [edi+312], eax
	mov DWORD PTR [edi+316], eax
21:
	mov ebx, edx
	movdqu xmm0, XMMWORD PTR [ebx+144]
	movdqu XMMWORD PTR [edi+1376], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+160]
	movdqu XMMWORD PTR [edi+1392], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+176]
	movdqu XMMWORD PTR [edi+1408], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+192]
	movdqu XMMWORD PTR [edi+1424], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+208]
	movdqu XMMWORD PTR [edi+1440], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+224]
	movdqu XMMWORD PTR [edi+1456], xmm0
	movdqu xmm0, XMMWORD PTR [edi+288]
	movdqu XMMWORD PTR [edi+1104], xmm0
	movdqu xmm0, XMMWORD PTR [edi+304]
	movdqu XMMWORD PTR [edi+1120], xmm0
	add edi, 384
	mov esi, edi
	add esi, 960
	movdqu xmm0, XMMWORD PTR [edi+720]
	movdqu xmm1, XMMWORD PTR [edi+736]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	movdqa xmm2, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm2, xmm1
	movdqa xmm6, xmm0
	pslld xmm6, 15
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+448], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 14
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+464], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 13
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+480], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 12
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+496], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 11
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 9
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 8
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+560], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 15
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+576], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 14
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+592], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 13
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+608], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 12
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+624], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 11
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+640], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+656], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 9
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+672], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 8
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+688], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+64]
	movdqu xmm6, XMMWORD PTR [esi+32]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm6
	pslld xmm2, 8
	psraw xmm2, 15
	pxor xmm1, xmm2
	movdqa xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm2, xmm6
	pslld xmm2, 15
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	movdqu xmm1, XMMWORD PTR [edi+464]
	movdqa xmm2, xmm6
	pslld xmm2, 14
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm2, xmm6
	pslld xmm2, 13
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm6
	pslld xmm2, 12
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm2, xmm6
	pslld xmm2, 11
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm6
	pslld xmm2, 10
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm6
	pslld xmm2, 9
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	pxor xmm0, xmm5
	pand xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm6
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi+128], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+144], xmm5
	movdqa xmm5, xmm2
	pand xmm5, xmm1
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	pxor xmm3, xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm7
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+192], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqa xmm1, xmm6
	pand xmm1, xmm5
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm7
	pxor xmm6, xmm2
	movdqa xmm7, xmm2
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+272], xmm2
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+288], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqa xmm0, xmm6
	pand xmm0, xmm5
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+320], xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+336], xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+144]
	pand xmm3, xmm5
	pxor xmm3, xmm0
	movdqu xmm0, XMMWORD PTR [edi+128]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+368], xmm5
	movdqa xmm5, xmm0
	pand xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm5
	pxor xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm3
	pxor xmm1, xmm7
	movdqu xmm3, XMMWORD PTR [edi+304]
	pxor xmm3, xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pxor xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+272]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+384], xmm6
	movdqu xmm6, XMMWORD PTR [edi+336]
	pand xmm6, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pxor xmm0, xmm6
	pxor xmm0, xmm2
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [edi]
	movdqu xmm2, XMMWORD PTR [edi+240]
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+352]
	pand xmm4, xmm2
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm4
	movdqa xmm4, xmm7
	pxor xmm4, xmm0
	pand xmm7, xmm3
	movdqa xmm6, xmm0
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm5
	pxor xmm7, xmm5
	pxor xmm3, xmm6
	movdqu xmm1, XMMWORD PTR [edi+208]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+160], xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm6
	pand xmm5, xmm1
	pxor xmm3, xmm5
	pxor xmm5, xmm7
	movdqu xmm1, XMMWORD PTR [edi+352]
	pand xmm1, xmm3
	pand xmm2, xmm3
	pand xmm7, xmm4
	pxor xmm7, xmm0
	pand xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	pand xmm0, xmm4
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+368]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+368], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+224], xmm4
	movdqu xmm4, XMMWORD PTR [edi+384]
	pand xmm4, xmm2
	movdqu XMMWORD PTR [edi+384], xmm4
	movdqu xmm4, XMMWORD PTR [edi+320]
	pand xmm4, xmm2
	pxor xmm0, xmm4
	pxor xmm4, xmm5
	pxor xmm4, xmm1
	pxor xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm7
	movdqu xmm2, XMMWORD PTR [edi+304]
	pand xmm2, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+224]
	pxor xmm4, xmm3
	pxor xmm7, xmm4
	movdqu xmm3, XMMWORD PTR [edi+288]
	pand xmm3, xmm4
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm7
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+272]
	pand xmm4, xmm7
	pxor xmm2, xmm1
	pxor xmm1, xmm0
	pxor xmm3, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+208]
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+400]
	pand xmm0, xmm6
	movdqu xmm7, XMMWORD PTR [edi+336]
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pxor xmm5, xmm7
	pxor xmm7, xmm3
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+368]
	pxor xmm7, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	pxor xmm0, xmm1
	pxor xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [edi+240]
	pxor xmm6, xmm4
	pxor xmm7, xmm1
	movdqu xmm4, XMMWORD PTR [edi+144]
	pxor xmm4, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+304]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+288]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi], xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm7
	movdqu xmm0, XMMWORD PTR [edi+160]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	movdqu xmm6, XMMWORD PTR [ebx+96]
	movdqu xmm7, XMMWORD PTR [ebx+112]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+576]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu xmm0, XMMWORD PTR [edi+16]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+592]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+592], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+608]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+608], xmm2
	movdqu xmm0, XMMWORD PTR [edi+48]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+624]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+624], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+640]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+640], xmm2
	movdqu xmm0, XMMWORD PTR [edi+80]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+656]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+656], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+672]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+672], xmm2
	movdqu xmm0, XMMWORD PTR [edi+112]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+688]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+688], xmm2
	movdqu xmm7, XMMWORD PTR [ebx+64]
	movdqu xmm6, XMMWORD PTR [esi+48]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm6
	pslld xmm2, 8
	psraw xmm2, 15
	pxor xmm1, xmm2
	movdqa xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm2, xmm6
	pslld xmm2, 15
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	movdqu xmm1, XMMWORD PTR [edi+592]
	movdqa xmm2, xmm6
	pslld xmm2, 14
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm2, xmm6
	pslld xmm2, 13
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm6
	pslld xmm2, 12
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm2, xmm6
	pslld xmm2, 11
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm6
	pslld xmm2, 10
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm6
	pslld xmm2, 9
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	pxor xmm0, xmm5
	pand xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm6
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi+128], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+144], xmm5
	movdqa xmm5, xmm2
	pand xmm5, xmm1
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	pxor xmm3, xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm7
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+192], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqa xmm1, xmm6
	pand xmm1, xmm5
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm7
	pxor xmm6, xmm2
	movdqa xmm7, xmm2
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+272], xmm2
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+288], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqa xmm0, xmm6
	pand xmm0, xmm5
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+320], xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+336], xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+144]
	pand xmm3, xmm5
	pxor xmm3, xmm0
	movdqu xmm0, XMMWORD PTR [edi+128]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+368], xmm5
	movdqa xmm5, xmm0
	pand xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm5
	pxor xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm3
	pxor xmm1, xmm7
	movdqu xmm3, XMMWORD PTR [edi+304]
	pxor xmm3, xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pxor xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+272]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+384], xmm6
	movdqu xmm6, XMMWORD PTR [edi+336]
	pand xmm6, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pxor xmm0, xmm6
	pxor xmm0, xmm2
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [edi]
	movdqu xmm2, XMMWORD PTR [edi+240]
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+352]
	pand xmm4, xmm2
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm4
	movdqa xmm4, xmm7
	pxor xmm4, xmm0
	pand xmm7, xmm3
	movdqa xmm6, xmm0
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm5
	pxor xmm7, xmm5
	pxor xmm3, xmm6
	movdqu xmm1, XMMWORD PTR [edi+208]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+160], xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm6
	pand xmm5, xmm1
	pxor xmm3, xmm5
	pxor xmm5, xmm7
	movdqu xmm1, XMMWORD PTR [edi+352]
	pand xmm1, xmm3
	pand xmm2, xmm3
	pand xmm7, xmm4
	pxor xmm7, xmm0
	pand xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	pand xmm0, xmm4
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+368]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+368], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+224], xmm4
	movdqu xmm4, XMMWORD PTR [edi+384]
	pand xmm4, xmm2
	movdqu XMMWORD PTR [edi+384], xmm4
	movdqu xmm4, XMMWORD PTR [edi+320]
	pand xmm4, xmm2
	pxor xmm0, xmm4
	pxor xmm4, xmm5
	pxor xmm4, xmm1
	pxor xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm7
	movdqu xmm2, XMMWORD PTR [edi+304]
	pand xmm2, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+224]
	pxor xmm4, xmm3
	pxor xmm7, xmm4
	movdqu xmm3, XMMWORD PTR [edi+288]
	pand xmm3, xmm4
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm7
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+272]
	pand xmm4, xmm7
	pxor xmm2, xmm1
	pxor xmm1, xmm0
	pxor xmm3, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+208]
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+400]
	pand xmm0, xmm6
	movdqu xmm7, XMMWORD PTR [edi+336]
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pxor xmm5, xmm7
	pxor xmm7, xmm3
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+368]
	pxor xmm7, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	pxor xmm0, xmm1
	pxor xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [edi+240]
	pxor xmm6, xmm4
	pxor xmm7, xmm1
	movdqu xmm4, XMMWORD PTR [edi+144]
	pxor xmm4, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+304]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+288]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi], xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm7
	movdqu xmm0, XMMWORD PTR [edi+160]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	movdqu xmm6, XMMWORD PTR [ebx+96]
	movdqu xmm7, XMMWORD PTR [ebx+112]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+448]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+448], xmm2
	movdqu xmm0, XMMWORD PTR [edi+16]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+464]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+480]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+480], xmm2
	movdqu xmm0, XMMWORD PTR [edi+48]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+496]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+496], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+512]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+512], xmm2
	movdqu xmm0, XMMWORD PTR [edi+80]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+528]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqu xmm0, XMMWORD PTR [edi+112]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+560]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqu xmm7, XMMWORD PTR [ebx+240]
	movdqu xmm0, XMMWORD PTR [edi+448]
	pand xmm0, xmm7
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+464]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+480]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+496]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+512]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+528]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+544]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+560]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 8
	pxor xmm0, xmm1
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqu xmm7, XMMWORD PTR [ebx+240]
	movdqu xmm2, XMMWORD PTR [edi+576]
	pand xmm2, xmm7
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+592]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+608]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+624]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+640]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+656]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+672]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+688]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	movdqa xmm1, xmm2
	psrld xmm1, 8
	pxor xmm2, xmm1
	pshuflw xmm2, xmm2, 216
	pshufhw xmm2, xmm2, 216
	pshufd xmm2, xmm2, 216
	punpcklqdq xmm0, xmm2
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu xmm1, XMMWORD PTR [edi+720]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+704], xmm0
	add esi, 32
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	movdqa xmm2, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm2, xmm1
	movdqa xmm6, xmm0
	pslld xmm6, 15
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+448], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 14
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+464], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 13
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+480], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 12
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+496], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 11
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 9
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 8
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+560], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 15
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+576], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 14
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+592], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 13
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+608], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 12
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+624], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 11
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+640], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+656], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 9
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+672], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 8
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+688], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+64]
	movdqu xmm6, XMMWORD PTR [esi+32]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm6
	pslld xmm2, 8
	psraw xmm2, 15
	pxor xmm1, xmm2
	movdqa xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm2, xmm6
	pslld xmm2, 15
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	movdqu xmm1, XMMWORD PTR [edi+464]
	movdqa xmm2, xmm6
	pslld xmm2, 14
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm2, xmm6
	pslld xmm2, 13
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm6
	pslld xmm2, 12
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm2, xmm6
	pslld xmm2, 11
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm6
	pslld xmm2, 10
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm6
	pslld xmm2, 9
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	pxor xmm0, xmm5
	pand xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm6
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi+128], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+144], xmm5
	movdqa xmm5, xmm2
	pand xmm5, xmm1
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	pxor xmm3, xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm7
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+192], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqa xmm1, xmm6
	pand xmm1, xmm5
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm7
	pxor xmm6, xmm2
	movdqa xmm7, xmm2
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+272], xmm2
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+288], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqa xmm0, xmm6
	pand xmm0, xmm5
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+320], xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+336], xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+144]
	pand xmm3, xmm5
	pxor xmm3, xmm0
	movdqu xmm0, XMMWORD PTR [edi+128]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+368], xmm5
	movdqa xmm5, xmm0
	pand xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm5
	pxor xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm3
	pxor xmm1, xmm7
	movdqu xmm3, XMMWORD PTR [edi+304]
	pxor xmm3, xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pxor xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+272]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+384], xmm6
	movdqu xmm6, XMMWORD PTR [edi+336]
	pand xmm6, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pxor xmm0, xmm6
	pxor xmm0, xmm2
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [edi]
	movdqu xmm2, XMMWORD PTR [edi+240]
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+352]
	pand xmm4, xmm2
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm4
	movdqa xmm4, xmm7
	pxor xmm4, xmm0
	pand xmm7, xmm3
	movdqa xmm6, xmm0
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm5
	pxor xmm7, xmm5
	pxor xmm3, xmm6
	movdqu xmm1, XMMWORD PTR [edi+208]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+160], xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm6
	pand xmm5, xmm1
	pxor xmm3, xmm5
	pxor xmm5, xmm7
	movdqu xmm1, XMMWORD PTR [edi+352]
	pand xmm1, xmm3
	pand xmm2, xmm3
	pand xmm7, xmm4
	pxor xmm7, xmm0
	pand xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	pand xmm0, xmm4
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+368]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+368], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+224], xmm4
	movdqu xmm4, XMMWORD PTR [edi+384]
	pand xmm4, xmm2
	movdqu XMMWORD PTR [edi+384], xmm4
	movdqu xmm4, XMMWORD PTR [edi+320]
	pand xmm4, xmm2
	pxor xmm0, xmm4
	pxor xmm4, xmm5
	pxor xmm4, xmm1
	pxor xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm7
	movdqu xmm2, XMMWORD PTR [edi+304]
	pand xmm2, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+224]
	pxor xmm4, xmm3
	pxor xmm7, xmm4
	movdqu xmm3, XMMWORD PTR [edi+288]
	pand xmm3, xmm4
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm7
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+272]
	pand xmm4, xmm7
	pxor xmm2, xmm1
	pxor xmm1, xmm0
	pxor xmm3, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+208]
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+400]
	pand xmm0, xmm6
	movdqu xmm7, XMMWORD PTR [edi+336]
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pxor xmm5, xmm7
	pxor xmm7, xmm3
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+368]
	pxor xmm7, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	pxor xmm0, xmm1
	pxor xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [edi+240]
	pxor xmm6, xmm4
	pxor xmm7, xmm1
	movdqu xmm4, XMMWORD PTR [edi+144]
	pxor xmm4, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+304]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+288]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi], xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm7
	movdqu xmm0, XMMWORD PTR [edi+160]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	movdqu xmm6, XMMWORD PTR [ebx+96]
	movdqu xmm7, XMMWORD PTR [ebx+112]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+576]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu xmm0, XMMWORD PTR [edi+16]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+592]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+592], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+608]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+608], xmm2
	movdqu xmm0, XMMWORD PTR [edi+48]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+624]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+624], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+640]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+640], xmm2
	movdqu xmm0, XMMWORD PTR [edi+80]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+656]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+656], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+672]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+672], xmm2
	movdqu xmm0, XMMWORD PTR [edi+112]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+688]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+688], xmm2
	movdqu xmm7, XMMWORD PTR [ebx+64]
	movdqu xmm6, XMMWORD PTR [esi+48]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm6
	pslld xmm2, 8
	psraw xmm2, 15
	pxor xmm1, xmm2
	movdqa xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm2, xmm6
	pslld xmm2, 15
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	movdqu xmm1, XMMWORD PTR [edi+592]
	movdqa xmm2, xmm6
	pslld xmm2, 14
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm2, xmm6
	pslld xmm2, 13
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm6
	pslld xmm2, 12
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm2, xmm6
	pslld xmm2, 11
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm6
	pslld xmm2, 10
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm6
	pslld xmm2, 9
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	pxor xmm0, xmm5
	pand xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm6
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi+128], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+144], xmm5
	movdqa xmm5, xmm2
	pand xmm5, xmm1
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	pxor xmm3, xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm7
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+192], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqa xmm1, xmm6
	pand xmm1, xmm5
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm7
	pxor xmm6, xmm2
	movdqa xmm7, xmm2
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+272], xmm2
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+288], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqa xmm0, xmm6
	pand xmm0, xmm5
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+320], xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+336], xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+144]
	pand xmm3, xmm5
	pxor xmm3, xmm0
	movdqu xmm0, XMMWORD PTR [edi+128]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+368], xmm5
	movdqa xmm5, xmm0
	pand xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm5
	pxor xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm3
	pxor xmm1, xmm7
	movdqu xmm3, XMMWORD PTR [edi+304]
	pxor xmm3, xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pxor xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+272]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+384], xmm6
	movdqu xmm6, XMMWORD PTR [edi+336]
	pand xmm6, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pxor xmm0, xmm6
	pxor xmm0, xmm2
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [edi]
	movdqu xmm2, XMMWORD PTR [edi+240]
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+352]
	pand xmm4, xmm2
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm4
	movdqa xmm4, xmm7
	pxor xmm4, xmm0
	pand xmm7, xmm3
	movdqa xmm6, xmm0
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm5
	pxor xmm7, xmm5
	pxor xmm3, xmm6
	movdqu xmm1, XMMWORD PTR [edi+208]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+160], xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm6
	pand xmm5, xmm1
	pxor xmm3, xmm5
	pxor xmm5, xmm7
	movdqu xmm1, XMMWORD PTR [edi+352]
	pand xmm1, xmm3
	pand xmm2, xmm3
	pand xmm7, xmm4
	pxor xmm7, xmm0
	pand xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	pand xmm0, xmm4
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+368]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+368], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+224], xmm4
	movdqu xmm4, XMMWORD PTR [edi+384]
	pand xmm4, xmm2
	movdqu XMMWORD PTR [edi+384], xmm4
	movdqu xmm4, XMMWORD PTR [edi+320]
	pand xmm4, xmm2
	pxor xmm0, xmm4
	pxor xmm4, xmm5
	pxor xmm4, xmm1
	pxor xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm7
	movdqu xmm2, XMMWORD PTR [edi+304]
	pand xmm2, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+224]
	pxor xmm4, xmm3
	pxor xmm7, xmm4
	movdqu xmm3, XMMWORD PTR [edi+288]
	pand xmm3, xmm4
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm7
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+272]
	pand xmm4, xmm7
	pxor xmm2, xmm1
	pxor xmm1, xmm0
	pxor xmm3, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+208]
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+400]
	pand xmm0, xmm6
	movdqu xmm7, XMMWORD PTR [edi+336]
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pxor xmm5, xmm7
	pxor xmm7, xmm3
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+368]
	pxor xmm7, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	pxor xmm0, xmm1
	pxor xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [edi+240]
	pxor xmm6, xmm4
	pxor xmm7, xmm1
	movdqu xmm4, XMMWORD PTR [edi+144]
	pxor xmm4, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+304]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+288]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi], xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm7
	movdqu xmm0, XMMWORD PTR [edi+160]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	movdqu xmm6, XMMWORD PTR [ebx+96]
	movdqu xmm7, XMMWORD PTR [ebx+112]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+448]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+448], xmm2
	movdqu xmm0, XMMWORD PTR [edi+16]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+464]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+480]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+480], xmm2
	movdqu xmm0, XMMWORD PTR [edi+48]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+496]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+496], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+512]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+512], xmm2
	movdqu xmm0, XMMWORD PTR [edi+80]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+528]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqu xmm0, XMMWORD PTR [edi+112]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+560]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqu xmm7, XMMWORD PTR [ebx+240]
	movdqu xmm0, XMMWORD PTR [edi+448]
	pand xmm0, xmm7
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+464]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+480]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+496]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+512]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+528]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+544]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+560]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 8
	pxor xmm0, xmm1
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqu xmm7, XMMWORD PTR [ebx+240]
	movdqu xmm2, XMMWORD PTR [edi+576]
	pand xmm2, xmm7
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+592]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+608]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+624]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+640]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+656]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+672]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+688]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	movdqa xmm1, xmm2
	psrld xmm1, 8
	pxor xmm2, xmm1
	pshuflw xmm2, xmm2, 216
	pshufhw xmm2, xmm2, 216
	pshufd xmm2, xmm2, 216
	punpcklqdq xmm0, xmm2
	movdqu XMMWORD PTR [edi+752], xmm0
	movdqu xmm0, XMMWORD PTR [edi+752]
	movdqu xmm1, XMMWORD PTR [edi+736]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+704], xmm0
	add esi, 32
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	movdqa xmm2, xmm0
	punpcklwd xmm0, xmm1
	punpckhwd xmm2, xmm1
	movdqa xmm6, xmm0
	pslld xmm6, 15
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+448], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 14
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+464], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 13
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+480], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 12
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+496], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 11
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 9
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm6, xmm0
	pslld xmm6, 8
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+560], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 15
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+576], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 14
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+592], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 13
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+608], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 12
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+624], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 11
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+640], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+656], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 9
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+672], xmm6
	movdqa xmm6, xmm2
	pslld xmm6, 8
	psraw xmm6, 15
	movdqu XMMWORD PTR [edi+688], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+64]
	movdqu xmm6, XMMWORD PTR [esi+32]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm6
	pslld xmm2, 8
	psraw xmm2, 15
	pxor xmm1, xmm2
	movdqa xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm2, xmm6
	pslld xmm2, 15
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	movdqu xmm1, XMMWORD PTR [edi+464]
	movdqa xmm2, xmm6
	pslld xmm2, 14
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm2, xmm6
	pslld xmm2, 13
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm6
	pslld xmm2, 12
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm2, xmm6
	pslld xmm2, 11
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm6
	pslld xmm2, 10
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm6
	pslld xmm2, 9
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	pxor xmm0, xmm5
	pand xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm6
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi+128], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+144], xmm5
	movdqa xmm5, xmm2
	pand xmm5, xmm1
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	pxor xmm3, xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm7
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+192], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqa xmm1, xmm6
	pand xmm1, xmm5
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm7
	pxor xmm6, xmm2
	movdqa xmm7, xmm2
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+272], xmm2
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+288], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqa xmm0, xmm6
	pand xmm0, xmm5
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+320], xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+336], xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+144]
	pand xmm3, xmm5
	pxor xmm3, xmm0
	movdqu xmm0, XMMWORD PTR [edi+128]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+368], xmm5
	movdqa xmm5, xmm0
	pand xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm5
	pxor xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm3
	pxor xmm1, xmm7
	movdqu xmm3, XMMWORD PTR [edi+304]
	pxor xmm3, xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pxor xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+272]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+384], xmm6
	movdqu xmm6, XMMWORD PTR [edi+336]
	pand xmm6, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pxor xmm0, xmm6
	pxor xmm0, xmm2
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [edi]
	movdqu xmm2, XMMWORD PTR [edi+240]
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+352]
	pand xmm4, xmm2
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm4
	movdqa xmm4, xmm7
	pxor xmm4, xmm0
	pand xmm7, xmm3
	movdqa xmm6, xmm0
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm5
	pxor xmm7, xmm5
	pxor xmm3, xmm6
	movdqu xmm1, XMMWORD PTR [edi+208]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+160], xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm6
	pand xmm5, xmm1
	pxor xmm3, xmm5
	pxor xmm5, xmm7
	movdqu xmm1, XMMWORD PTR [edi+352]
	pand xmm1, xmm3
	pand xmm2, xmm3
	pand xmm7, xmm4
	pxor xmm7, xmm0
	pand xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	pand xmm0, xmm4
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+368]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+368], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+224], xmm4
	movdqu xmm4, XMMWORD PTR [edi+384]
	pand xmm4, xmm2
	movdqu XMMWORD PTR [edi+384], xmm4
	movdqu xmm4, XMMWORD PTR [edi+320]
	pand xmm4, xmm2
	pxor xmm0, xmm4
	pxor xmm4, xmm5
	pxor xmm4, xmm1
	pxor xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm7
	movdqu xmm2, XMMWORD PTR [edi+304]
	pand xmm2, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+224]
	pxor xmm4, xmm3
	pxor xmm7, xmm4
	movdqu xmm3, XMMWORD PTR [edi+288]
	pand xmm3, xmm4
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm7
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+272]
	pand xmm4, xmm7
	pxor xmm2, xmm1
	pxor xmm1, xmm0
	pxor xmm3, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+208]
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+400]
	pand xmm0, xmm6
	movdqu xmm7, XMMWORD PTR [edi+336]
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pxor xmm5, xmm7
	pxor xmm7, xmm3
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+368]
	pxor xmm7, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	pxor xmm0, xmm1
	pxor xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [edi+240]
	pxor xmm6, xmm4
	pxor xmm7, xmm1
	movdqu xmm4, XMMWORD PTR [edi+144]
	pxor xmm4, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+304]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+288]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi], xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm7
	movdqu xmm0, XMMWORD PTR [edi+160]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	movdqu xmm6, XMMWORD PTR [ebx+96]
	movdqu xmm7, XMMWORD PTR [ebx+112]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+576]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu xmm0, XMMWORD PTR [edi+16]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+592]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+592], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+608]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+608], xmm2
	movdqu xmm0, XMMWORD PTR [edi+48]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+624]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+624], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+640]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+640], xmm2
	movdqu xmm0, XMMWORD PTR [edi+80]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+656]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+656], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+672]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+672], xmm2
	movdqu xmm0, XMMWORD PTR [edi+112]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+688]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+688], xmm2
	movdqu xmm7, XMMWORD PTR [ebx+64]
	movdqu xmm6, XMMWORD PTR [esi+48]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm6
	pslld xmm2, 8
	psraw xmm2, 15
	pxor xmm1, xmm2
	movdqa xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm2, xmm6
	pslld xmm2, 15
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi], xmm1
	movdqu xmm1, XMMWORD PTR [edi+592]
	movdqa xmm2, xmm6
	pslld xmm2, 14
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm2, xmm6
	pslld xmm2, 13
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+32], xmm1
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm6
	pslld xmm2, 12
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm2, xmm6
	pslld xmm2, 11
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+64], xmm1
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm6
	pslld xmm2, 10
	psraw xmm2, 15
	pxor xmm1, xmm2
	pxor xmm0, xmm1
	pand xmm0, xmm7
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm6
	pslld xmm2, 9
	psraw xmm2, 15
	pxor xmm0, xmm2
	pxor xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+96], xmm1
	pxor xmm0, xmm5
	pand xmm0, xmm7
	pxor xmm0, xmm5
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+96]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi+80]
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm6
	movdqu xmm2, XMMWORD PTR [edi+112]
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu XMMWORD PTR [edi+128], xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+144], xmm5
	movdqa xmm5, xmm2
	pand xmm5, xmm1
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	pxor xmm3, xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm7
	movdqu xmm7, XMMWORD PTR [edi+32]
	movdqu XMMWORD PTR [edi+192], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqa xmm1, xmm6
	pand xmm1, xmm5
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm7
	pxor xmm6, xmm2
	movdqa xmm7, xmm2
	pand xmm7, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+272], xmm2
	movdqa xmm2, xmm0
	pand xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+80]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+288], xmm6
	movdqu xmm6, XMMWORD PTR [edi+80]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqa xmm0, xmm6
	pand xmm0, xmm5
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+320], xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+336], xmm5
	movdqu xmm5, XMMWORD PTR [edi+208]
	pxor xmm5, xmm4
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+144]
	pand xmm3, xmm5
	pxor xmm3, xmm0
	movdqu xmm0, XMMWORD PTR [edi+128]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+368], xmm5
	movdqa xmm5, xmm0
	pand xmm5, xmm4
	pxor xmm7, xmm5
	pxor xmm2, xmm5
	pxor xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [edi+192]
	pxor xmm5, xmm3
	pxor xmm1, xmm7
	movdqu xmm3, XMMWORD PTR [edi+304]
	pxor xmm3, xmm1
	movdqa xmm1, xmm3
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+32]
	pxor xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+272]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+384], xmm6
	movdqu xmm6, XMMWORD PTR [edi+336]
	pand xmm6, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+176]
	pxor xmm0, xmm6
	pxor xmm0, xmm2
	pxor xmm0, xmm4
	movdqu xmm4, XMMWORD PTR [edi]
	movdqu xmm2, XMMWORD PTR [edi+240]
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [edi+352]
	pand xmm4, xmm2
	pxor xmm4, xmm6
	pxor xmm4, xmm7
	movdqu xmm7, XMMWORD PTR [edi+128]
	pxor xmm7, xmm4
	movdqa xmm4, xmm7
	pxor xmm4, xmm0
	pand xmm7, xmm3
	movdqa xmm6, xmm0
	pxor xmm6, xmm7
	pand xmm6, xmm1
	pxor xmm6, xmm5
	pxor xmm7, xmm5
	pxor xmm3, xmm6
	movdqu xmm1, XMMWORD PTR [edi+208]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm6
	movdqu XMMWORD PTR [edi+160], xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm6
	pand xmm5, xmm1
	pxor xmm3, xmm5
	pxor xmm5, xmm7
	movdqu xmm1, XMMWORD PTR [edi+352]
	pand xmm1, xmm3
	pand xmm2, xmm3
	pand xmm7, xmm4
	pxor xmm7, xmm0
	pand xmm5, xmm7
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	pand xmm0, xmm4
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [edi+368]
	pand xmm0, xmm7
	movdqu XMMWORD PTR [edi+368], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+224], xmm4
	movdqu xmm4, XMMWORD PTR [edi+384]
	pand xmm4, xmm2
	movdqu XMMWORD PTR [edi+384], xmm4
	movdqu xmm4, XMMWORD PTR [edi+320]
	pand xmm4, xmm2
	pxor xmm0, xmm4
	pxor xmm4, xmm5
	pxor xmm4, xmm1
	pxor xmm7, xmm6
	movdqu xmm5, XMMWORD PTR [edi+192]
	pand xmm5, xmm7
	movdqu xmm2, XMMWORD PTR [edi+304]
	pand xmm2, xmm7
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+304], xmm4
	movdqu xmm4, XMMWORD PTR [edi+224]
	pxor xmm4, xmm3
	pxor xmm7, xmm4
	movdqu xmm3, XMMWORD PTR [edi+288]
	pand xmm3, xmm4
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm7
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [edi+272]
	pand xmm4, xmm7
	pxor xmm2, xmm1
	pxor xmm1, xmm0
	pxor xmm3, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [edi+208]
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+400]
	pand xmm0, xmm6
	movdqu xmm7, XMMWORD PTR [edi+336]
	pand xmm7, xmm6
	pxor xmm2, xmm7
	pxor xmm5, xmm7
	pxor xmm7, xmm3
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+160], xmm7
	movdqu xmm7, XMMWORD PTR [edi+368]
	pxor xmm7, xmm6
	pxor xmm3, xmm0
	pxor xmm3, xmm5
	pxor xmm0, xmm1
	pxor xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [edi+240]
	pxor xmm6, xmm4
	pxor xmm7, xmm1
	movdqu xmm4, XMMWORD PTR [edi+144]
	pxor xmm4, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [edi+304]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [edi+288]
	pxor xmm5, xmm6
	movdqu XMMWORD PTR [edi], xmm3
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+96], xmm1
	movdqu XMMWORD PTR [edi+112], xmm7
	movdqu xmm0, XMMWORD PTR [edi+160]
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm5, XMMWORD PTR [ebx+80]
	movdqu xmm6, XMMWORD PTR [ebx+96]
	movdqu xmm7, XMMWORD PTR [ebx+112]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+448]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+448], xmm2
	movdqu xmm0, XMMWORD PTR [edi+16]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+464]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+16]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+480]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+480], xmm2
	movdqu xmm0, XMMWORD PTR [edi+48]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+32]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+496]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+496], xmm2
	movdqu xmm0, XMMWORD PTR [edi+64]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+48]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+512]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+512], xmm2
	movdqu xmm0, XMMWORD PTR [edi+80]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+64]
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+528]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu xmm0, XMMWORD PTR [edi+96]
	pandn xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+80]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+112]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqu xmm0, XMMWORD PTR [edi+112]
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+96]
	pandn xmm1, xmm6
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pshufd xmm1, xmm0, 238
	pshufd xmm2, xmm0, 68
	pxor xmm2, xmm1
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	pxor xmm1, xmm2
	pshuflw xmm3, xmm2, 57
	pxor xmm1, xmm3
	pshufd xmm3, xmm1, 177
	pxor xmm2, xmm3
	punpcklqdq xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [edi+560]
	pxor xmm2, xmm3
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqu xmm7, XMMWORD PTR [ebx+240]
	movdqu xmm0, XMMWORD PTR [edi+448]
	pand xmm0, xmm7
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+464]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+480]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+496]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+512]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+528]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+544]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+560]
	pand xmm1, xmm7
	pxor xmm0, xmm1
	movdqa xmm1, xmm0
	psrld xmm1, 8
	pxor xmm0, xmm1
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	movdqu xmm7, XMMWORD PTR [ebx+240]
	movdqu xmm2, XMMWORD PTR [edi+576]
	pand xmm2, xmm7
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+592]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+608]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+624]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+640]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+656]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+672]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	pslld xmm7, 1
	movdqu xmm1, XMMWORD PTR [edi+688]
	pand xmm1, xmm7
	pxor xmm2, xmm1
	movdqa xmm1, xmm2
	psrld xmm1, 8
	pxor xmm2, xmm1
	pshuflw xmm2, xmm2, 216
	pshufhw xmm2, xmm2, 216
	pshufd xmm2, xmm2, 216
	punpcklqdq xmm0, xmm2
	movdqu XMMWORD PTR [edi+768], xmm0
	sub edi, 384
	movdqu xmm0, XMMWORD PTR [edi+1136]
	movdqu XMMWORD PTR [edi+336], xmm0
	movdqu xmm0, XMMWORD PTR [edi+1152]
	movdqu XMMWORD PTR [edi+352], xmm0
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edi+288], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edi+292], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edi+296], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edi+300], eax
	mov eax, DWORD PTR [edi+304]
	bswap eax
	mov DWORD PTR [edi+304], eax
	mov eax, DWORD PTR [edi+308]
	bswap eax
	mov DWORD PTR [edi+308], eax
	mov eax, DWORD PTR [edi+312]
	bswap eax
	mov DWORD PTR [edi+312], eax
	mov eax, DWORD PTR [edi+316]
	bswap eax
	mov DWORD PTR [edi+316], eax
	mov eax, DWORD PTR [edi+336]
	bswap eax
	mov DWORD PTR [edi+336], eax
	mov eax, DWORD PTR [edi+340]
	bswap eax
	mov DWORD PTR [edi+340], eax
	mov eax, DWORD PTR [edi+344]
	bswap eax
	mov DWORD PTR [edi+344], eax
	mov eax, DWORD PTR [edi+348]
	bswap eax
	mov DWORD PTR [edi+348], eax
	mov eax, DWORD PTR [edi+352]
	bswap eax
	mov DWORD PTR [edi+352], eax
	mov eax, DWORD PTR [edi+356]
	bswap eax
	mov DWORD PTR [edi+356], eax
	mov eax, DWORD PTR [edi+360]
	bswap eax
	mov DWORD PTR [edi+360], eax
	mov eax, DWORD PTR [edi+364]
	bswap eax
	mov DWORD PTR [edi+364], eax
	mov edx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esp+8]
	cmp eax, 16
	je 24f
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+352]
	bswap eax
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+356]
	bswap eax
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+360]
	bswap eax
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+364]
	bswap eax
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+124], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+128], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+132], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+136], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+140], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+144], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+148], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+152], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+156], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+160], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+164], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+168], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+172], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+176], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+180], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+184], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+188], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+192], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+196], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+200], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+204], eax
	mov eax, DWORD PTR [edi+312]
	mov ebx, DWORD PTR [edi+316]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+208], eax
	mov eax, DWORD PTR [edi+316]
	mov ebx, DWORD PTR [edi+304]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+212], eax
	mov eax, DWORD PTR [edi+304]
	mov ebx, DWORD PTR [edi+308]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+216], eax
	mov eax, DWORD PTR [edi+308]
	mov ebx, DWORD PTR [edi+312]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+220], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+224], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+228], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+232], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+236], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+240], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+244], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+248], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+252], eax
	mov eax, DWORD PTR [edi+364]
	mov ebx, DWORD PTR [edi+352]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+256], eax
	mov eax, DWORD PTR [edi+352]
	mov ebx, DWORD PTR [edi+356]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+260], eax
	mov eax, DWORD PTR [edi+356]
	mov ebx, DWORD PTR [edi+360]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+264], eax
	mov eax, DWORD PTR [edi+360]
	mov ebx, DWORD PTR [edi+364]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+268], eax
	jmp 25f
24:
	mov eax, DWORD PTR [edi+288]
	bswap eax
	mov DWORD PTR [edx], eax
	mov eax, DWORD PTR [edi+292]
	bswap eax
	mov DWORD PTR [edx+4], eax
	mov eax, DWORD PTR [edi+296]
	bswap eax
	mov DWORD PTR [edx+8], eax
	mov eax, DWORD PTR [edi+300]
	bswap eax
	mov DWORD PTR [edx+12], eax
	mov eax, DWORD PTR [edi+336]
	bswap eax
	mov DWORD PTR [edx+16], eax
	mov eax, DWORD PTR [edi+340]
	bswap eax
	mov DWORD PTR [edx+20], eax
	mov eax, DWORD PTR [edi+344]
	bswap eax
	mov DWORD PTR [edx+24], eax
	mov eax, DWORD PTR [edi+348]
	bswap eax
	mov DWORD PTR [edx+28], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+32], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+36], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+40], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+44], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+48], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+52], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+56], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+60], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+64], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+68], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+72], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+76], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+80], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+84], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+88], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+92], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+96], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+100], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+104], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+108], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+112], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+116], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+120], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 4
	and eax, -268435456
	shr ebx, 4
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+124], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+128], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+132], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+136], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 19
	and eax, -8192
	shr ebx, 19
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+140], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+144], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+148], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+152], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+156], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+160], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+164], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+168], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 2
	and eax, -1073741824
	shr ebx, 2
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+172], eax
	mov eax, DWORD PTR [edi+300]
	mov ebx, DWORD PTR [edi+288]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+176], eax
	mov eax, DWORD PTR [edi+288]
	mov ebx, DWORD PTR [edi+292]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+180], eax
	mov eax, DWORD PTR [edi+292]
	mov ebx, DWORD PTR [edi+296]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+184], eax
	mov eax, DWORD PTR [edi+296]
	mov ebx, DWORD PTR [edi+300]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+188], eax
	mov eax, DWORD PTR [edi+348]
	mov ebx, DWORD PTR [edi+336]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+192], eax
	mov eax, DWORD PTR [edi+336]
	mov ebx, DWORD PTR [edi+340]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+196], eax
	mov eax, DWORD PTR [edi+340]
	mov ebx, DWORD PTR [edi+344]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+200], eax
	mov eax, DWORD PTR [edi+344]
	mov ebx, DWORD PTR [edi+348]
	ror eax, 17
	and eax, -32768
	shr ebx, 17
	or eax, ebx
	bswap eax
	mov DWORD PTR [edx+204], eax
25:
	mov ebx, DWORD PTR [edi+368]
	mov esi, DWORD PTR [edi+372]
	mov ebp, DWORD PTR [edi+380]
	mov edi, DWORD PTR [edi+376]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+20], xmm0
	movdqu XMMWORD PTR [esp+36], xmm0
	movdqu XMMWORD PTR [esp+52], xmm0
	movdqu XMMWORD PTR [esp+68], xmm0
	movdqu XMMWORD PTR [esp+84], xmm0
	movdqu XMMWORD PTR [esp+100], xmm0
	movdqu XMMWORD PTR [esp+116], xmm0
	movdqu XMMWORD PTR [esp+132], xmm0
	movdqu XMMWORD PTR [esp+148], xmm0
	movdqu XMMWORD PTR [esp+164], xmm0
	movdqu XMMWORD PTR [esp+180], xmm0
	movdqu XMMWORD PTR [esp+196], xmm0
	movdqu XMMWORD PTR [esp+212], xmm0
	movdqu XMMWORD PTR [esp+228], xmm0
	movdqu XMMWORD PTR [esp+244], xmm0
	movdqu XMMWORD PTR [esp+260], xmm0
	movdqu XMMWORD PTR [esp+276], xmm0
	movdqu XMMWORD PTR [esp+292], xmm0
	movdqu XMMWORD PTR [esp+308], xmm0
	movdqu XMMWORD PTR [esp+324], xmm0
	movdqu XMMWORD PTR [esp+340], xmm0
	movdqu XMMWORD PTR [esp+356], xmm0
	movdqu XMMWORD PTR [esp+372], xmm0
	movdqu XMMWORD PTR [esp+388], xmm0
	movdqu XMMWORD PTR [esp+404], xmm0
	movdqu XMMWORD PTR [esp+420], xmm0
	movdqu XMMWORD PTR [esp+436], xmm0
	movdqu XMMWORD PTR [esp+452], xmm0
	movdqu XMMWORD PTR [esp+468], xmm0
	movdqu XMMWORD PTR [esp+484], xmm0
	movdqu XMMWORD PTR [esp+500], xmm0
	movdqu XMMWORD PTR [esp+516], xmm0
	movdqu XMMWORD PTR [esp+532], xmm0
	movdqu XMMWORD PTR [esp+548], xmm0
	movdqu XMMWORD PTR [esp+564], xmm0
	movdqu XMMWORD PTR [esp+580], xmm0
	movdqu XMMWORD PTR [esp+596], xmm0
	movdqu XMMWORD PTR [esp+612], xmm0
	movdqu XMMWORD PTR [esp+628], xmm0
	movdqu XMMWORD PTR [esp+644], xmm0
	movdqu XMMWORD PTR [esp+660], xmm0
	movdqu XMMWORD PTR [esp+676], xmm0
	movdqu XMMWORD PTR [esp+692], xmm0
	movdqu XMMWORD PTR [esp+708], xmm0
	movdqu XMMWORD PTR [esp+724], xmm0
	movdqu XMMWORD PTR [esp+740], xmm0
	movdqu XMMWORD PTR [esp+756], xmm0
	movdqu XMMWORD PTR [esp+772], xmm0
	movdqu XMMWORD PTR [esp+788], xmm0
	movdqu XMMWORD PTR [esp+804], xmm0
	movdqu XMMWORD PTR [esp+820], xmm0
	movdqu XMMWORD PTR [esp+836], xmm0
	movdqu XMMWORD PTR [esp+852], xmm0
	movdqu XMMWORD PTR [esp+868], xmm0
	movdqu XMMWORD PTR [esp+884], xmm0
	movdqu XMMWORD PTR [esp+900], xmm0
	movdqu XMMWORD PTR [esp+916], xmm0
	movdqu XMMWORD PTR [esp+932], xmm0
	movdqu XMMWORD PTR [esp+948], xmm0
	movdqu XMMWORD PTR [esp+964], xmm0
	movdqu XMMWORD PTR [esp+980], xmm0
	movdqu XMMWORD PTR [esp+996], xmm0
	movdqu XMMWORD PTR [esp+1012], xmm0
	movdqu XMMWORD PTR [esp+1028], xmm0
	movdqu XMMWORD PTR [esp+1044], xmm0
	movdqu XMMWORD PTR [esp+1060], xmm0
	movdqu XMMWORD PTR [esp+1076], xmm0
	movdqu XMMWORD PTR [esp+1092], xmm0
	movdqu XMMWORD PTR [esp+1108], xmm0
	movdqu XMMWORD PTR [esp+1124], xmm0
	movdqu XMMWORD PTR [esp+1140], xmm0
	movdqu XMMWORD PTR [esp+1156], xmm0
	movdqu XMMWORD PTR [esp+1172], xmm0
	movdqu XMMWORD PTR [esp+1188], xmm0
	movdqu XMMWORD PTR [esp+1204], xmm0
	movdqu XMMWORD PTR [esp+1220], xmm0
	movdqu XMMWORD PTR [esp+1236], xmm0
	movdqu XMMWORD PTR [esp+1252], xmm0
	movdqu XMMWORD PTR [esp+1268], xmm0
	movdqu XMMWORD PTR [esp+1284], xmm0
	movdqu XMMWORD PTR [esp+1300], xmm0
	movdqu XMMWORD PTR [esp+1316], xmm0
	movdqu XMMWORD PTR [esp+1332], xmm0
	movdqu XMMWORD PTR [esp+1348], xmm0
	movdqu XMMWORD PTR [esp+1364], xmm0
	movdqu XMMWORD PTR [esp+1380], xmm0
	movdqu XMMWORD PTR [esp+1396], xmm0
	movdqu XMMWORD PTR [esp+1412], xmm0
	movdqu XMMWORD PTR [esp+1428], xmm0
	movdqu XMMWORD PTR [esp+1444], xmm0
	movdqu XMMWORD PTR [esp+1460], xmm0
	movdqu XMMWORD PTR [esp+1476], xmm0
	lea esp, [esp+1504]
	lea esp, [esp-1508]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+1496], ecx
	mov DWORD PTR [esp+1500], ecx
	mov DWORD PTR [esp+1504], ecx
	lea esp, [esp+1508]
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

vg_camellia_ecb_encrypt_aesni:
	lea esp, [esp-884]
	mov eax, DWORD PTR [esp+888]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+892]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+896]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+900]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+816], ebx
	mov DWORD PTR [eax+820], esi
	mov DWORD PTR [eax+824], edi
	mov DWORD PTR [eax+828], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI_WIDE}
	pop ecx
	mov esi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI}
	pop ecx
	mov DWORD PTR [edi], esi
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [eax+16]
	movdqu XMMWORD PTR [edi+560], xmm0
	movdqu xmm0, XMMWORD PTR [eax+32]
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm0, XMMWORD PTR [eax+48]
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm0, XMMWORD PTR [eax+64]
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm0, XMMWORD PTR [eax+80]
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm0, XMMWORD PTR [eax+96]
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm0, XMMWORD PTR [eax+112]
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm0, XMMWORD PTR [eax+128]
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm0, XMMWORD PTR [eax+144]
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu xmm0, XMMWORD PTR [eax+160]
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm0, XMMWORD PTR [eax+176]
	movdqu XMMWORD PTR [edi+720], xmm0
	movdqu xmm0, XMMWORD PTR [eax+192]
	movdqu XMMWORD PTR [edi+736], xmm0
	movdqu xmm0, XMMWORD PTR [eax+208]
	movdqu XMMWORD PTR [edi+752], xmm0
	movdqu xmm0, XMMWORD PTR [eax+224]
	movdqu XMMWORD PTR [edi+768], xmm0
	movdqu xmm0, XMMWORD PTR [eax+240]
	movdqu XMMWORD PTR [edi+784], xmm0
	movdqu xmm0, XMMWORD PTR [eax+256]
	movdqu XMMWORD PTR [edi+800], xmm0
	mov eax, edi
	add eax, 544
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqa xmm6, xmm2
20:
	movdqu xmm0, XMMWORD PTR [eax+16]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqa xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+464]
	pxor xmm0, xmm5
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	pxor xmm6, xmm6
	movdqu xmm0, XMMWORD PTR [eax+32]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+480]
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [esi+16], xmm5
	movdqa xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [eax+48]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+480]
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [esi+32], xmm5
	movdqu xmm0, XMMWORD PTR [ebx+496]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [esi+48], xmm2
	sub ecx, 1
	je 21f
	movdqu xmm0, XMMWORD PTR [eax+64]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+400]
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pand xmm1, xmm2
	movdqu XMMWORD PTR [esi+64], xmm1
	movdqa xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+432]
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pand xmm1, xmm2
	movdqu XMMWORD PTR [esi+80], xmm1
	psrlq xmm0, 32
	movdqu XMMWORD PTR [esi+96], xmm0
	add eax, 64
	add esi, 112
	test ecx, ecx
	jmp 22f
21:
22:
	jne 20b
	movdqu xmm0, XMMWORD PTR [eax+64]
	movdqu XMMWORD PTR [esi+64], xmm0
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+836]
	cmp eax, 4
	jb 23f
25:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+576]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	pshufb xmm0, xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm0
	punpcklqdq xmm1, xmm0
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm4, xmm6
	pand xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm6
	pxor xmm5, xmm1
	movq xmm4, QWORD PTR [esi]
	punpcklqdq xmm4, xmm4
	pxor xmm5, xmm4
	movdqu XMMWORD PTR [edi+512], xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm3
	pshufb xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm2, xmm0
	movq xmm6, QWORD PTR [esi+8]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm4
	punpcklqdq xmm1, xmm4
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+80]
	pshufb xmm1, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movq xmm0, QWORD PTR [esi]
	punpcklqdq xmm0, xmm0
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+64]
	pshufb xmm4, xmm3
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movq xmm0, QWORD PTR [esi+8]
	punpcklqdq xmm0, xmm0
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [edi+560], xmm5
26:
	movdqu xmm0, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+256]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm6, xmm3
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm0
	pxor xmm1, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm6, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm0
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu XMMWORD PTR [edi+560], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+16]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	movq xmm2, QWORD PTR [esi+16]
	punpcklqdq xmm2, xmm2
	pxor xmm1, xmm2
	movdqa xmm2, xmm7
	pand xmm2, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm6
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm6
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm6, XMMWORD PTR [edi+528]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm3, QWORD PTR [esi+24]
	punpcklqdq xmm3, xmm3
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm2, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+24]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqu XMMWORD PTR [edi+560], xmm0
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+32]
	punpcklqdq xmm3, xmm3
	pxor xmm1, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+544]
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm2, QWORD PTR [esi+32]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+240]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu XMMWORD PTR [edi+544], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm3, QWORD PTR [esi+40]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+176]
	pshufb xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	movq xmm4, QWORD PTR [esi+40]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqa xmm3, xmm7
	pand xmm3, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm2
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm6
	pxor xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm6, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm5
	movq xmm4, QWORD PTR [esi+48]
	punpcklqdq xmm4, xmm4
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+48]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm5
	pxor xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	sub ecx, 1
	je 27f
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movq xmm0, QWORD PTR [esi+64]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm1, QWORD PTR [esi+64]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm2
	psrlq xmm1, 32
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	pslld xmm3, 1
	por xmm3, xmm0
	psllq xmm3, 32
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+96]
	punpcklqdq xmm4, xmm4
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [edi+560]
	movq xmm6, QWORD PTR [esi+56]
	punpcklqdq xmm6, xmm6
	pxor xmm5, xmm6
	movdqa xmm4, xmm7
	pand xmm4, xmm5
	psrld xmm5, 4
	pand xmm5, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm5
	pxor xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movq xmm0, QWORD PTR [esi+80]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm3, QWORD PTR [esi+80]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	psrlq xmm3, 32
	movq xmm4, QWORD PTR [esi+80]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm2
	pslld xmm4, 1
	por xmm4, xmm0
	psllq xmm4, 32
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqa xmm5, xmm7
	pand xmm5, xmm2
	psrld xmm2, 4
	pand xmm2, xmm7
	movq xmm1, QWORD PTR [esi+72]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm6
	psrld xmm1, 31
	movq xmm0, QWORD PTR [esi+72]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm6
	psrlq xmm0, 32
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	pslld xmm3, 1
	por xmm3, xmm1
	psllq xmm3, 32
	pxor xmm6, xmm3
	pxor xmm6, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pand xmm5, xmm4
	pand xmm4, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+64]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movq xmm2, QWORD PTR [esi+104]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm4, QWORD PTR [esi+112]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+512], xmm1
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+88]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm6
	psrlq xmm5, 32
	movq xmm4, QWORD PTR [esi+88]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm6
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm6, xmm4
	pxor xmm6, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+112]
	pshufb xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm2, xmm3
	pand xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm1
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+72]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrlq xmm5, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movq xmm4, QWORD PTR [esi+72]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm1
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm0, xmm3
	pand xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm6
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm0
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+544]
	movq xmm4, QWORD PTR [esi+104]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrld xmm5, 31
	movq xmm6, QWORD PTR [esi+120]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm3
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movq xmm0, QWORD PTR [esi+88]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm1
	psrlq xmm0, 32
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm6
	pxor xmm4, xmm2
	movq xmm6, QWORD PTR [esi+88]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm1
	pslld xmm6, 1
	por xmm6, xmm5
	psllq xmm6, 32
	pxor xmm1, xmm6
	pxor xmm1, xmm0
	movq xmm5, QWORD PTR [esi+64]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrld xmm5, 31
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm4
	psrlq xmm3, 32
	movq xmm2, QWORD PTR [esi+64]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	pslld xmm2, 1
	por xmm2, xmm5
	psllq xmm2, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm0
	movq xmm5, QWORD PTR [esi+96]
	punpcklqdq xmm5, xmm5
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm3, xmm0
	movq xmm1, QWORD PTR [esi+120]
	punpcklqdq xmm1, xmm1
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+528], xmm3
	movq xmm2, QWORD PTR [esi+80]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	psrld xmm2, 31
	movq xmm5, QWORD PTR [esi+80]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrlq xmm5, 32
	movq xmm6, QWORD PTR [esi+80]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm4
	pslld xmm6, 1
	por xmm6, xmm2
	psllq xmm6, 32
	pxor xmm4, xmm6
	pxor xmm4, xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm4
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+32]
	pand xmm0, xmm2
	pand xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm4
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm1, xmm6
	movq xmm0, QWORD PTR [esi+112]
	punpcklqdq xmm0, xmm0
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	add esi, 112
	test ecx, ecx
	jmp 28f
27:
28:
	jne 26b
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm1, QWORD PTR [esi+56]
	punpcklqdq xmm1, xmm1
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	movdqa xmm4, xmm7
	pand xmm4, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm4, xmm1
	pand xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm4, xmm5
	punpcklqdq xmm4, xmm2
	punpckhqdq xmm5, xmm2
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm2
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [esi+64]
	pxor xmm4, xmm2
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+576], xmm4
	movdqu XMMWORD PTR [edi+592], xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm2, xmm1
	pand xmm1, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm3, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqa xmm4, xmm3
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm6
	pshufb xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm4, xmm6
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+608], xmm4
	movdqu XMMWORD PTR [edi+624], xmm3
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	cmp ebp, 4
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+836]
	cmp eax, 2
	jb 29f
211:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+604], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+576]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	pshufb xmm0, xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm0
	punpcklqdq xmm1, xmm0
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm4, xmm6
	pand xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm6
	pxor xmm5, xmm1
	movq xmm4, QWORD PTR [esi]
	punpcklqdq xmm4, xmm4
	pxor xmm5, xmm4
	movdqu XMMWORD PTR [edi+512], xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm3
	pshufb xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm2, xmm0
	movq xmm6, QWORD PTR [esi+8]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm4
	punpcklqdq xmm1, xmm4
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+80]
	pshufb xmm1, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movq xmm0, QWORD PTR [esi]
	punpcklqdq xmm0, xmm0
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+64]
	pshufb xmm4, xmm3
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movq xmm0, QWORD PTR [esi+8]
	punpcklqdq xmm0, xmm0
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [edi+560], xmm5
212:
	movdqu xmm0, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+256]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm6, xmm3
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm0
	pxor xmm1, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm6, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm0
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu XMMWORD PTR [edi+560], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+16]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	movq xmm2, QWORD PTR [esi+16]
	punpcklqdq xmm2, xmm2
	pxor xmm1, xmm2
	movdqa xmm2, xmm7
	pand xmm2, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm6
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm6
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm6, XMMWORD PTR [edi+528]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm3, QWORD PTR [esi+24]
	punpcklqdq xmm3, xmm3
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm2, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+24]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqu XMMWORD PTR [edi+560], xmm0
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+32]
	punpcklqdq xmm3, xmm3
	pxor xmm1, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+544]
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm2, QWORD PTR [esi+32]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+240]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu XMMWORD PTR [edi+544], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm3, QWORD PTR [esi+40]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+176]
	pshufb xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	movq xmm4, QWORD PTR [esi+40]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqa xmm3, xmm7
	pand xmm3, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm2
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm6
	pxor xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm6, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm5
	movq xmm4, QWORD PTR [esi+48]
	punpcklqdq xmm4, xmm4
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+48]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm5
	pxor xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	sub ecx, 1
	je 213f
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movq xmm0, QWORD PTR [esi+64]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm1, QWORD PTR [esi+64]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm2
	psrlq xmm1, 32
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	pslld xmm3, 1
	por xmm3, xmm0
	psllq xmm3, 32
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+96]
	punpcklqdq xmm4, xmm4
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [edi+560]
	movq xmm6, QWORD PTR [esi+56]
	punpcklqdq xmm6, xmm6
	pxor xmm5, xmm6
	movdqa xmm4, xmm7
	pand xmm4, xmm5
	psrld xmm5, 4
	pand xmm5, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm5
	pxor xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movq xmm0, QWORD PTR [esi+80]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm3, QWORD PTR [esi+80]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	psrlq xmm3, 32
	movq xmm4, QWORD PTR [esi+80]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm2
	pslld xmm4, 1
	por xmm4, xmm0
	psllq xmm4, 32
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqa xmm5, xmm7
	pand xmm5, xmm2
	psrld xmm2, 4
	pand xmm2, xmm7
	movq xmm1, QWORD PTR [esi+72]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm6
	psrld xmm1, 31
	movq xmm0, QWORD PTR [esi+72]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm6
	psrlq xmm0, 32
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	pslld xmm3, 1
	por xmm3, xmm1
	psllq xmm3, 32
	pxor xmm6, xmm3
	pxor xmm6, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pand xmm5, xmm4
	pand xmm4, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+64]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movq xmm2, QWORD PTR [esi+104]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm4, QWORD PTR [esi+112]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+512], xmm1
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+88]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm6
	psrlq xmm5, 32
	movq xmm4, QWORD PTR [esi+88]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm6
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm6, xmm4
	pxor xmm6, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+112]
	pshufb xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm2, xmm3
	pand xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm1
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+72]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrlq xmm5, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movq xmm4, QWORD PTR [esi+72]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm1
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm0, xmm3
	pand xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm6
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm0
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+544]
	movq xmm4, QWORD PTR [esi+104]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrld xmm5, 31
	movq xmm6, QWORD PTR [esi+120]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm3
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movq xmm0, QWORD PTR [esi+88]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm1
	psrlq xmm0, 32
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm6
	pxor xmm4, xmm2
	movq xmm6, QWORD PTR [esi+88]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm1
	pslld xmm6, 1
	por xmm6, xmm5
	psllq xmm6, 32
	pxor xmm1, xmm6
	pxor xmm1, xmm0
	movq xmm5, QWORD PTR [esi+64]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrld xmm5, 31
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm4
	psrlq xmm3, 32
	movq xmm2, QWORD PTR [esi+64]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	pslld xmm2, 1
	por xmm2, xmm5
	psllq xmm2, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm0
	movq xmm5, QWORD PTR [esi+96]
	punpcklqdq xmm5, xmm5
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm3, xmm0
	movq xmm1, QWORD PTR [esi+120]
	punpcklqdq xmm1, xmm1
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+528], xmm3
	movq xmm2, QWORD PTR [esi+80]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	psrld xmm2, 31
	movq xmm5, QWORD PTR [esi+80]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrlq xmm5, 32
	movq xmm6, QWORD PTR [esi+80]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm4
	pslld xmm6, 1
	por xmm6, xmm2
	psllq xmm6, 32
	pxor xmm4, xmm6
	pxor xmm4, xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm4
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+32]
	pand xmm0, xmm2
	pand xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm4
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm1, xmm6
	movq xmm0, QWORD PTR [esi+112]
	punpcklqdq xmm0, xmm0
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	add esi, 112
	test ecx, ecx
	jmp 214f
213:
214:
	jne 212b
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm1, QWORD PTR [esi+56]
	punpcklqdq xmm1, xmm1
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	movdqa xmm4, xmm7
	pand xmm4, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm4, xmm1
	pand xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm4, xmm5
	punpcklqdq xmm4, xmm2
	punpckhqdq xmm5, xmm2
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm2
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [esi+64]
	pxor xmm4, xmm2
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+576], xmm4
	movdqu XMMWORD PTR [edi+592], xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm2, xmm1
	pand xmm1, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm3, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqa xmm4, xmm3
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm6
	pshufb xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm4, xmm6
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+608], xmm4
	movdqu XMMWORD PTR [edi+624], xmm3
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	cmp ebp, 2
	jae 211b
	jmp 210f
29:
210:
	mov eax, DWORD PTR [edi+836]
	test eax, eax
	je 215f
217:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+588], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+576]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	pshufb xmm0, xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm0
	punpcklqdq xmm1, xmm0
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm4, xmm6
	pand xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm6
	pxor xmm5, xmm1
	movq xmm4, QWORD PTR [esi]
	punpcklqdq xmm4, xmm4
	pxor xmm5, xmm4
	movdqu XMMWORD PTR [edi+512], xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm3
	pshufb xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm2, xmm0
	movq xmm6, QWORD PTR [esi+8]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm4
	punpcklqdq xmm1, xmm4
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+80]
	pshufb xmm1, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movq xmm0, QWORD PTR [esi]
	punpcklqdq xmm0, xmm0
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+64]
	pshufb xmm4, xmm3
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movq xmm0, QWORD PTR [esi+8]
	punpcklqdq xmm0, xmm0
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [edi+560], xmm5
218:
	movdqu xmm0, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+256]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm6, xmm3
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm0
	pxor xmm1, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm6, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm0
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu XMMWORD PTR [edi+560], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+16]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	movq xmm2, QWORD PTR [esi+16]
	punpcklqdq xmm2, xmm2
	pxor xmm1, xmm2
	movdqa xmm2, xmm7
	pand xmm2, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm6
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm6
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm6, XMMWORD PTR [edi+528]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm3, QWORD PTR [esi+24]
	punpcklqdq xmm3, xmm3
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm2, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+24]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqu XMMWORD PTR [edi+560], xmm0
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+32]
	punpcklqdq xmm3, xmm3
	pxor xmm1, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+544]
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm2, QWORD PTR [esi+32]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+240]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu XMMWORD PTR [edi+544], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm3, QWORD PTR [esi+40]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+176]
	pshufb xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	movq xmm4, QWORD PTR [esi+40]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqa xmm3, xmm7
	pand xmm3, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm2
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm6
	pxor xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm6, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm5
	movq xmm4, QWORD PTR [esi+48]
	punpcklqdq xmm4, xmm4
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+48]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm5
	pxor xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	sub ecx, 1
	je 219f
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movq xmm0, QWORD PTR [esi+64]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm1, QWORD PTR [esi+64]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm2
	psrlq xmm1, 32
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	pslld xmm3, 1
	por xmm3, xmm0
	psllq xmm3, 32
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+96]
	punpcklqdq xmm4, xmm4
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [edi+560]
	movq xmm6, QWORD PTR [esi+56]
	punpcklqdq xmm6, xmm6
	pxor xmm5, xmm6
	movdqa xmm4, xmm7
	pand xmm4, xmm5
	psrld xmm5, 4
	pand xmm5, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm5
	pxor xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movq xmm0, QWORD PTR [esi+80]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm3, QWORD PTR [esi+80]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	psrlq xmm3, 32
	movq xmm4, QWORD PTR [esi+80]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm2
	pslld xmm4, 1
	por xmm4, xmm0
	psllq xmm4, 32
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqa xmm5, xmm7
	pand xmm5, xmm2
	psrld xmm2, 4
	pand xmm2, xmm7
	movq xmm1, QWORD PTR [esi+72]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm6
	psrld xmm1, 31
	movq xmm0, QWORD PTR [esi+72]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm6
	psrlq xmm0, 32
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	pslld xmm3, 1
	por xmm3, xmm1
	psllq xmm3, 32
	pxor xmm6, xmm3
	pxor xmm6, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pand xmm5, xmm4
	pand xmm4, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+64]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movq xmm2, QWORD PTR [esi+104]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm4, QWORD PTR [esi+112]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+512], xmm1
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+88]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm6
	psrlq xmm5, 32
	movq xmm4, QWORD PTR [esi+88]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm6
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm6, xmm4
	pxor xmm6, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+112]
	pshufb xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm2, xmm3
	pand xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm1
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+72]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrlq xmm5, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movq xmm4, QWORD PTR [esi+72]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm1
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm0, xmm3
	pand xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm6
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm0
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+544]
	movq xmm4, QWORD PTR [esi+104]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrld xmm5, 31
	movq xmm6, QWORD PTR [esi+120]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm3
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movq xmm0, QWORD PTR [esi+88]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm1
	psrlq xmm0, 32
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm6
	pxor xmm4, xmm2
	movq xmm6, QWORD PTR [esi+88]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm1
	pslld xmm6, 1
	por xmm6, xmm5
	psllq xmm6, 32
	pxor xmm1, xmm6
	pxor xmm1, xmm0
	movq xmm5, QWORD PTR [esi+64]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrld xmm5, 31
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm4
	psrlq xmm3, 32
	movq xmm2, QWORD PTR [esi+64]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	pslld xmm2, 1
	por xmm2, xmm5
	psllq xmm2, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm0
	movq xmm5, QWORD PTR [esi+96]
	punpcklqdq xmm5, xmm5
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm3, xmm0
	movq xmm1, QWORD PTR [esi+120]
	punpcklqdq xmm1, xmm1
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+528], xmm3
	movq xmm2, QWORD PTR [esi+80]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	psrld xmm2, 31
	movq xmm5, QWORD PTR [esi+80]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrlq xmm5, 32
	movq xmm6, QWORD PTR [esi+80]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm4
	pslld xmm6, 1
	por xmm6, xmm2
	psllq xmm6, 32
	pxor xmm4, xmm6
	pxor xmm4, xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm4
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+32]
	pand xmm0, xmm2
	pand xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm4
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm1, xmm6
	movq xmm0, QWORD PTR [esi+112]
	punpcklqdq xmm0, xmm0
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	add esi, 112
	test ecx, ecx
	jmp 220f
219:
220:
	jne 218b
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm1, QWORD PTR [esi+56]
	punpcklqdq xmm1, xmm1
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	movdqa xmm4, xmm7
	pand xmm4, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm4, xmm1
	pand xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm4, xmm5
	punpcklqdq xmm4, xmm2
	punpckhqdq xmm5, xmm2
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm2
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [esi+64]
	pxor xmm4, xmm2
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+576], xmm4
	movdqu XMMWORD PTR [edi+592], xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm2, xmm1
	pand xmm1, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm3, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqa xmm4, xmm3
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm6
	pshufb xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm4, xmm6
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+608], xmm4
	movdqu XMMWORD PTR [edi+624], xmm3
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	jne 217b
	jmp 216f
215:
216:
	mov ebx, DWORD PTR [edi+816]
	mov esi, DWORD PTR [edi+820]
	mov ebp, DWORD PTR [edi+828]
	mov edi, DWORD PTR [edi+824]
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
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	lea esp, [esp+884]
	lea esp, [esp-888]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+884], ecx
	lea esp, [esp+888]
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

vg_camellia_ecb_encrypt:
	lea esp, [esp-1572]
	mov eax, DWORD PTR [esp+1576]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_SSE2}
	pop ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, edi
	add esi, 960
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm6, XMMWORD PTR [ebx+128]
	cmp ecx, 18
	je 20f
	mov ecx, 34
	jmp 21f
20:
	mov ecx, 26
21:
22:
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	add eax, 8
	sub ecx, 1
	jne 22b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 16
	jb 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+956], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [edi+944]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [edi+948]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [edi+952]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [edi+956]
	mov DWORD PTR [esi+252], eax
	add esi, 256
	sub ebp, 16
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 16
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 8
	jb 26f
28:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+828], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 8
	jae 28b
	jmp 27f
26:
27:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 4
	jb 29f
211:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+764], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 4
	jae 211b
	jmp 210f
29:
210:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 2
	jb 212f
214:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 2
	jae 214b
	jmp 213f
212:
213:
	mov eax, DWORD PTR [edi+1524]
	test eax, eax
	je 215f
217:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jne 217b
	jmp 216f
215:
216:
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
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
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	movdqu XMMWORD PTR [esp+968], xmm0
	movdqu XMMWORD PTR [esp+984], xmm0
	movdqu XMMWORD PTR [esp+1000], xmm0
	movdqu XMMWORD PTR [esp+1016], xmm0
	movdqu XMMWORD PTR [esp+1032], xmm0
	movdqu XMMWORD PTR [esp+1048], xmm0
	movdqu XMMWORD PTR [esp+1064], xmm0
	movdqu XMMWORD PTR [esp+1080], xmm0
	movdqu XMMWORD PTR [esp+1096], xmm0
	movdqu XMMWORD PTR [esp+1112], xmm0
	movdqu XMMWORD PTR [esp+1128], xmm0
	movdqu XMMWORD PTR [esp+1144], xmm0
	movdqu XMMWORD PTR [esp+1160], xmm0
	movdqu XMMWORD PTR [esp+1176], xmm0
	movdqu XMMWORD PTR [esp+1192], xmm0
	movdqu XMMWORD PTR [esp+1208], xmm0
	movdqu XMMWORD PTR [esp+1224], xmm0
	movdqu XMMWORD PTR [esp+1240], xmm0
	movdqu XMMWORD PTR [esp+1256], xmm0
	movdqu XMMWORD PTR [esp+1272], xmm0
	movdqu XMMWORD PTR [esp+1288], xmm0
	movdqu XMMWORD PTR [esp+1304], xmm0
	movdqu XMMWORD PTR [esp+1320], xmm0
	movdqu XMMWORD PTR [esp+1336], xmm0
	movdqu XMMWORD PTR [esp+1352], xmm0
	movdqu XMMWORD PTR [esp+1368], xmm0
	movdqu XMMWORD PTR [esp+1384], xmm0
	movdqu XMMWORD PTR [esp+1400], xmm0
	movdqu XMMWORD PTR [esp+1416], xmm0
	movdqu XMMWORD PTR [esp+1432], xmm0
	movdqu XMMWORD PTR [esp+1448], xmm0
	movdqu XMMWORD PTR [esp+1464], xmm0
	movdqu XMMWORD PTR [esp+1480], xmm0
	movdqu XMMWORD PTR [esp+1496], xmm0
	movdqu XMMWORD PTR [esp+1512], xmm0
	movdqu XMMWORD PTR [esp+1528], xmm0
	movdqu XMMWORD PTR [esp+1544], xmm0
	mov DWORD PTR [esp+1560], ecx
	mov DWORD PTR [esp+1564], ecx
	lea esp, [esp+1572]
	lea esp, [esp-1576]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+1572], ecx
	lea esp, [esp+1576]
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

vg_camellia_ecb_decrypt_aesni:
	lea esp, [esp-884]
	mov eax, DWORD PTR [esp+888]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+892]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+896]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+900]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+816], ebx
	mov DWORD PTR [eax+820], esi
	mov DWORD PTR [eax+824], edi
	mov DWORD PTR [eax+828], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI_WIDE}
	pop ecx
	mov esi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI}
	pop ecx
	mov DWORD PTR [edi], esi
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	cmp ecx, 3
	je 20f
	movdqu xmm0, XMMWORD PTR [eax+256]
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [eax+240]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+560], xmm0
	movdqu xmm0, XMMWORD PTR [eax+224]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm0, XMMWORD PTR [eax+208]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm0, XMMWORD PTR [eax+192]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm0, XMMWORD PTR [eax+176]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm0, XMMWORD PTR [eax+160]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm0, XMMWORD PTR [eax+144]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm0, XMMWORD PTR [eax+128]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm0, XMMWORD PTR [eax+112]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu xmm0, XMMWORD PTR [eax+96]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm0, XMMWORD PTR [eax+80]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+720], xmm0
	movdqu xmm0, XMMWORD PTR [eax+64]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+736], xmm0
	movdqu xmm0, XMMWORD PTR [eax+48]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+752], xmm0
	movdqu xmm0, XMMWORD PTR [eax+32]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+768], xmm0
	movdqu xmm0, XMMWORD PTR [eax+16]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+784], xmm0
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [edi+800], xmm0
	jmp 21f
20:
	movdqu xmm0, XMMWORD PTR [eax+192]
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [eax+176]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+560], xmm0
	movdqu xmm0, XMMWORD PTR [eax+160]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm0, XMMWORD PTR [eax+144]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm0, XMMWORD PTR [eax+128]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm0, XMMWORD PTR [eax+112]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm0, XMMWORD PTR [eax+96]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm0, XMMWORD PTR [eax+80]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm0, XMMWORD PTR [eax+64]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm0, XMMWORD PTR [eax+48]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu xmm0, XMMWORD PTR [eax+32]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm0, XMMWORD PTR [eax+16]
	pshufd xmm0, xmm0, 78
	movdqu XMMWORD PTR [edi+720], xmm0
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu XMMWORD PTR [edi+736], xmm0
21:
	mov eax, edi
	add eax, 544
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [eax]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqa xmm6, xmm2
22:
	movdqu xmm0, XMMWORD PTR [eax+16]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	movdqa xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+464]
	pxor xmm0, xmm5
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	pxor xmm6, xmm6
	movdqu xmm0, XMMWORD PTR [eax+32]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+480]
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [esi+16], xmm5
	movdqa xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [eax+48]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm3
	pxor xmm2, xmm4
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+480]
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [esi+32], xmm5
	movdqu xmm0, XMMWORD PTR [ebx+496]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [esi+48], xmm2
	sub ecx, 1
	je 23f
	movdqu xmm0, XMMWORD PTR [eax+64]
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm0, xmm1
	movdqa xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+400]
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pand xmm1, xmm2
	movdqu XMMWORD PTR [esi+64], xmm1
	movdqa xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+432]
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pand xmm1, xmm2
	movdqu XMMWORD PTR [esi+80], xmm1
	psrlq xmm0, 32
	movdqu XMMWORD PTR [esi+96], xmm0
	add eax, 64
	add esi, 112
	test ecx, ecx
	jmp 24f
23:
24:
	jne 22b
	movdqu xmm0, XMMWORD PTR [eax+64]
	movdqu XMMWORD PTR [esi+64], xmm0
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+836]
	cmp eax, 4
	jb 25f
27:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+576]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	pshufb xmm0, xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm0
	punpcklqdq xmm1, xmm0
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm4, xmm6
	pand xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm6
	pxor xmm5, xmm1
	movq xmm4, QWORD PTR [esi]
	punpcklqdq xmm4, xmm4
	pxor xmm5, xmm4
	movdqu XMMWORD PTR [edi+512], xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm3
	pshufb xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm2, xmm0
	movq xmm6, QWORD PTR [esi+8]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm4
	punpcklqdq xmm1, xmm4
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+80]
	pshufb xmm1, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movq xmm0, QWORD PTR [esi]
	punpcklqdq xmm0, xmm0
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+64]
	pshufb xmm4, xmm3
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movq xmm0, QWORD PTR [esi+8]
	punpcklqdq xmm0, xmm0
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [edi+560], xmm5
28:
	movdqu xmm0, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+256]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm6, xmm3
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm0
	pxor xmm1, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm6, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm0
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu XMMWORD PTR [edi+560], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+16]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	movq xmm2, QWORD PTR [esi+16]
	punpcklqdq xmm2, xmm2
	pxor xmm1, xmm2
	movdqa xmm2, xmm7
	pand xmm2, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm6
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm6
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm6, XMMWORD PTR [edi+528]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm3, QWORD PTR [esi+24]
	punpcklqdq xmm3, xmm3
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm2, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+24]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqu XMMWORD PTR [edi+560], xmm0
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+32]
	punpcklqdq xmm3, xmm3
	pxor xmm1, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+544]
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm2, QWORD PTR [esi+32]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+240]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu XMMWORD PTR [edi+544], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm3, QWORD PTR [esi+40]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+176]
	pshufb xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	movq xmm4, QWORD PTR [esi+40]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqa xmm3, xmm7
	pand xmm3, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm2
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm6
	pxor xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm6, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm5
	movq xmm4, QWORD PTR [esi+48]
	punpcklqdq xmm4, xmm4
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+48]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm5
	pxor xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	sub ecx, 1
	je 29f
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movq xmm0, QWORD PTR [esi+64]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm1, QWORD PTR [esi+64]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm2
	psrlq xmm1, 32
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	pslld xmm3, 1
	por xmm3, xmm0
	psllq xmm3, 32
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+96]
	punpcklqdq xmm4, xmm4
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [edi+560]
	movq xmm6, QWORD PTR [esi+56]
	punpcklqdq xmm6, xmm6
	pxor xmm5, xmm6
	movdqa xmm4, xmm7
	pand xmm4, xmm5
	psrld xmm5, 4
	pand xmm5, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm5
	pxor xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movq xmm0, QWORD PTR [esi+80]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm3, QWORD PTR [esi+80]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	psrlq xmm3, 32
	movq xmm4, QWORD PTR [esi+80]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm2
	pslld xmm4, 1
	por xmm4, xmm0
	psllq xmm4, 32
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqa xmm5, xmm7
	pand xmm5, xmm2
	psrld xmm2, 4
	pand xmm2, xmm7
	movq xmm1, QWORD PTR [esi+72]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm6
	psrld xmm1, 31
	movq xmm0, QWORD PTR [esi+72]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm6
	psrlq xmm0, 32
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	pslld xmm3, 1
	por xmm3, xmm1
	psllq xmm3, 32
	pxor xmm6, xmm3
	pxor xmm6, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pand xmm5, xmm4
	pand xmm4, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+64]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movq xmm2, QWORD PTR [esi+104]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm4, QWORD PTR [esi+112]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+512], xmm1
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+88]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm6
	psrlq xmm5, 32
	movq xmm4, QWORD PTR [esi+88]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm6
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm6, xmm4
	pxor xmm6, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+112]
	pshufb xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm2, xmm3
	pand xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm1
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+72]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrlq xmm5, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movq xmm4, QWORD PTR [esi+72]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm1
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm0, xmm3
	pand xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm6
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm0
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+544]
	movq xmm4, QWORD PTR [esi+104]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrld xmm5, 31
	movq xmm6, QWORD PTR [esi+120]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm3
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movq xmm0, QWORD PTR [esi+88]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm1
	psrlq xmm0, 32
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm6
	pxor xmm4, xmm2
	movq xmm6, QWORD PTR [esi+88]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm1
	pslld xmm6, 1
	por xmm6, xmm5
	psllq xmm6, 32
	pxor xmm1, xmm6
	pxor xmm1, xmm0
	movq xmm5, QWORD PTR [esi+64]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrld xmm5, 31
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm4
	psrlq xmm3, 32
	movq xmm2, QWORD PTR [esi+64]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	pslld xmm2, 1
	por xmm2, xmm5
	psllq xmm2, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm0
	movq xmm5, QWORD PTR [esi+96]
	punpcklqdq xmm5, xmm5
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm3, xmm0
	movq xmm1, QWORD PTR [esi+120]
	punpcklqdq xmm1, xmm1
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+528], xmm3
	movq xmm2, QWORD PTR [esi+80]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	psrld xmm2, 31
	movq xmm5, QWORD PTR [esi+80]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrlq xmm5, 32
	movq xmm6, QWORD PTR [esi+80]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm4
	pslld xmm6, 1
	por xmm6, xmm2
	psllq xmm6, 32
	pxor xmm4, xmm6
	pxor xmm4, xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm4
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+32]
	pand xmm0, xmm2
	pand xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm4
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm1, xmm6
	movq xmm0, QWORD PTR [esi+112]
	punpcklqdq xmm0, xmm0
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	add esi, 112
	test ecx, ecx
	jmp 210f
29:
210:
	jne 28b
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm1, QWORD PTR [esi+56]
	punpcklqdq xmm1, xmm1
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	movdqa xmm4, xmm7
	pand xmm4, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm4, xmm1
	pand xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm4, xmm5
	punpcklqdq xmm4, xmm2
	punpckhqdq xmm5, xmm2
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm2
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [esi+64]
	pxor xmm4, xmm2
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+576], xmm4
	movdqu XMMWORD PTR [edi+592], xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm2, xmm1
	pand xmm1, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm3, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqa xmm4, xmm3
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm6
	pshufb xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm4, xmm6
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+608], xmm4
	movdqu XMMWORD PTR [edi+624], xmm3
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	cmp ebp, 4
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+836]
	cmp eax, 2
	jb 211f
213:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+604], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+576]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	pshufb xmm0, xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm0
	punpcklqdq xmm1, xmm0
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm4, xmm6
	pand xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm6
	pxor xmm5, xmm1
	movq xmm4, QWORD PTR [esi]
	punpcklqdq xmm4, xmm4
	pxor xmm5, xmm4
	movdqu XMMWORD PTR [edi+512], xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm3
	pshufb xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm2, xmm0
	movq xmm6, QWORD PTR [esi+8]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm4
	punpcklqdq xmm1, xmm4
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+80]
	pshufb xmm1, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movq xmm0, QWORD PTR [esi]
	punpcklqdq xmm0, xmm0
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+64]
	pshufb xmm4, xmm3
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movq xmm0, QWORD PTR [esi+8]
	punpcklqdq xmm0, xmm0
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [edi+560], xmm5
214:
	movdqu xmm0, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+256]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm6, xmm3
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm0
	pxor xmm1, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm6, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm0
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu XMMWORD PTR [edi+560], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+16]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	movq xmm2, QWORD PTR [esi+16]
	punpcklqdq xmm2, xmm2
	pxor xmm1, xmm2
	movdqa xmm2, xmm7
	pand xmm2, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm6
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm6
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm6, XMMWORD PTR [edi+528]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm3, QWORD PTR [esi+24]
	punpcklqdq xmm3, xmm3
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm2, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+24]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqu XMMWORD PTR [edi+560], xmm0
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+32]
	punpcklqdq xmm3, xmm3
	pxor xmm1, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+544]
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm2, QWORD PTR [esi+32]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+240]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu XMMWORD PTR [edi+544], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm3, QWORD PTR [esi+40]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+176]
	pshufb xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	movq xmm4, QWORD PTR [esi+40]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqa xmm3, xmm7
	pand xmm3, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm2
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm6
	pxor xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm6, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm5
	movq xmm4, QWORD PTR [esi+48]
	punpcklqdq xmm4, xmm4
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+48]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm5
	pxor xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	sub ecx, 1
	je 215f
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movq xmm0, QWORD PTR [esi+64]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm1, QWORD PTR [esi+64]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm2
	psrlq xmm1, 32
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	pslld xmm3, 1
	por xmm3, xmm0
	psllq xmm3, 32
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+96]
	punpcklqdq xmm4, xmm4
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [edi+560]
	movq xmm6, QWORD PTR [esi+56]
	punpcklqdq xmm6, xmm6
	pxor xmm5, xmm6
	movdqa xmm4, xmm7
	pand xmm4, xmm5
	psrld xmm5, 4
	pand xmm5, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm5
	pxor xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movq xmm0, QWORD PTR [esi+80]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm3, QWORD PTR [esi+80]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	psrlq xmm3, 32
	movq xmm4, QWORD PTR [esi+80]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm2
	pslld xmm4, 1
	por xmm4, xmm0
	psllq xmm4, 32
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqa xmm5, xmm7
	pand xmm5, xmm2
	psrld xmm2, 4
	pand xmm2, xmm7
	movq xmm1, QWORD PTR [esi+72]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm6
	psrld xmm1, 31
	movq xmm0, QWORD PTR [esi+72]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm6
	psrlq xmm0, 32
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	pslld xmm3, 1
	por xmm3, xmm1
	psllq xmm3, 32
	pxor xmm6, xmm3
	pxor xmm6, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pand xmm5, xmm4
	pand xmm4, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+64]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movq xmm2, QWORD PTR [esi+104]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm4, QWORD PTR [esi+112]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+512], xmm1
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+88]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm6
	psrlq xmm5, 32
	movq xmm4, QWORD PTR [esi+88]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm6
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm6, xmm4
	pxor xmm6, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+112]
	pshufb xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm2, xmm3
	pand xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm1
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+72]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrlq xmm5, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movq xmm4, QWORD PTR [esi+72]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm1
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm0, xmm3
	pand xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm6
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm0
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+544]
	movq xmm4, QWORD PTR [esi+104]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrld xmm5, 31
	movq xmm6, QWORD PTR [esi+120]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm3
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movq xmm0, QWORD PTR [esi+88]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm1
	psrlq xmm0, 32
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm6
	pxor xmm4, xmm2
	movq xmm6, QWORD PTR [esi+88]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm1
	pslld xmm6, 1
	por xmm6, xmm5
	psllq xmm6, 32
	pxor xmm1, xmm6
	pxor xmm1, xmm0
	movq xmm5, QWORD PTR [esi+64]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrld xmm5, 31
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm4
	psrlq xmm3, 32
	movq xmm2, QWORD PTR [esi+64]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	pslld xmm2, 1
	por xmm2, xmm5
	psllq xmm2, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm0
	movq xmm5, QWORD PTR [esi+96]
	punpcklqdq xmm5, xmm5
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm3, xmm0
	movq xmm1, QWORD PTR [esi+120]
	punpcklqdq xmm1, xmm1
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+528], xmm3
	movq xmm2, QWORD PTR [esi+80]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	psrld xmm2, 31
	movq xmm5, QWORD PTR [esi+80]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrlq xmm5, 32
	movq xmm6, QWORD PTR [esi+80]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm4
	pslld xmm6, 1
	por xmm6, xmm2
	psllq xmm6, 32
	pxor xmm4, xmm6
	pxor xmm4, xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm4
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+32]
	pand xmm0, xmm2
	pand xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm4
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm1, xmm6
	movq xmm0, QWORD PTR [esi+112]
	punpcklqdq xmm0, xmm0
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	add esi, 112
	test ecx, ecx
	jmp 216f
215:
216:
	jne 214b
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm1, QWORD PTR [esi+56]
	punpcklqdq xmm1, xmm1
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	movdqa xmm4, xmm7
	pand xmm4, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm4, xmm1
	pand xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm4, xmm5
	punpcklqdq xmm4, xmm2
	punpckhqdq xmm5, xmm2
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm2
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [esi+64]
	pxor xmm4, xmm2
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+576], xmm4
	movdqu XMMWORD PTR [edi+592], xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm2, xmm1
	pand xmm1, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm3, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqa xmm4, xmm3
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm6
	pshufb xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm4, xmm6
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+608], xmm4
	movdqu XMMWORD PTR [edi+624], xmm3
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+592]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+596]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+600]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+604]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	cmp ebp, 2
	jae 213b
	jmp 212f
211:
212:
	mov eax, DWORD PTR [edi+836]
	test eax, eax
	je 217f
219:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+588], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+576]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	pshufb xmm0, xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm0
	punpcklqdq xmm1, xmm0
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm4, xmm6
	pand xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+64]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+80]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+96]
	pshufb xmm1, xmm6
	pxor xmm5, xmm1
	movq xmm4, QWORD PTR [esi]
	punpcklqdq xmm4, xmm4
	pxor xmm5, xmm4
	movdqu XMMWORD PTR [edi+512], xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqu xmm4, XMMWORD PTR [edi+624]
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm3
	pxor xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm3
	pshufb xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm2, xmm0
	movq xmm6, QWORD PTR [esi+8]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqa xmm3, xmm1
	punpckhqdq xmm3, xmm4
	punpcklqdq xmm1, xmm4
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+80]
	pshufb xmm1, xmm4
	pxor xmm6, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+96]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movq xmm0, QWORD PTR [esi]
	punpcklqdq xmm0, xmm0
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [edi+544], xmm6
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+64]
	pshufb xmm4, xmm3
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movq xmm0, QWORD PTR [esi+8]
	punpcklqdq xmm0, xmm0
	pxor xmm5, xmm0
	movdqu XMMWORD PTR [edi+560], xmm5
220:
	movdqu xmm0, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+256]
	pshufb xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm6, xmm3
	pshufb xmm6, xmm5
	pxor xmm1, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm0
	pxor xmm1, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+288]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm6, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+208]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm0
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu XMMWORD PTR [edi+560], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+16]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm0, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	movq xmm2, QWORD PTR [esi+16]
	punpcklqdq xmm2, xmm2
	pxor xmm1, xmm2
	movdqa xmm2, xmm7
	pand xmm2, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm6
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm1, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm1, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm6
	pxor xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm6, XMMWORD PTR [edi+528]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm3, QWORD PTR [esi+24]
	punpcklqdq xmm3, xmm3
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm2, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+24]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm1
	pxor xmm5, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm4
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu XMMWORD PTR [edi+528], xmm6
	movdqu XMMWORD PTR [edi+560], xmm0
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	movq xmm3, QWORD PTR [esi+32]
	punpcklqdq xmm3, xmm3
	pxor xmm1, xmm3
	movdqa xmm4, xmm7
	pand xmm4, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm3
	pxor xmm1, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm3, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm3, xmm2
	pxor xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm3, xmm6
	pxor xmm2, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+192]
	pshufb xmm4, xmm6
	pxor xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	aesenclast xmm0, xmm7
	movdqu xmm6, XMMWORD PTR [edi+544]
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movq xmm2, QWORD PTR [esi+32]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+272]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm2
	pxor xmm6, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+448]
	pshufb xmm3, xmm2
	pxor xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+240]
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+256]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm5, xmm3
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu XMMWORD PTR [edi+544], xmm6
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm3, QWORD PTR [esi+40]
	punpcklqdq xmm3, xmm3
	pxor xmm0, xmm3
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+272]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm5
	pxor xmm0, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm3
	pxor xmm0, xmm5
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+176]
	pshufb xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	aesenclast xmm6, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	movq xmm4, QWORD PTR [esi+40]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqa xmm3, xmm7
	pand xmm3, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+272]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+288]
	pshufb xmm2, xmm6
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm5, xmm6
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+400]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm2
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm2
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+208]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm6
	pxor xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+384]
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+304]
	movdqa xmm4, xmm5
	pshufb xmm4, xmm6
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm6
	pxor xmm1, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm5
	pshufb xmm3, xmm6
	pxor xmm1, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+352]
	pshufb xmm5, xmm6
	pxor xmm1, xmm5
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm6, XMMWORD PTR [edi+512]
	aesenclast xmm0, xmm7
	movdqa xmm5, xmm7
	pand xmm5, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm5
	movq xmm4, QWORD PTR [esi+48]
	punpcklqdq xmm4, xmm4
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+288]
	pshufb xmm3, xmm0
	pxor xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+432]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm4
	pxor xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+240]
	pshufb xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm0
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm4
	pshufb xmm2, xmm3
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+416]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+176]
	pshufb xmm3, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm0
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+192]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+368]
	movdqa xmm5, xmm4
	pshufb xmm5, xmm0
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+304]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+320]
	movdqa xmm2, xmm3
	pshufb xmm2, xmm0
	pxor xmm6, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+336]
	movdqa xmm4, xmm3
	pshufb xmm4, xmm0
	pxor xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+352]
	pshufb xmm3, xmm0
	pxor xmm6, xmm3
	aesenclast xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm3, xmm7
	pand xmm3, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movq xmm5, QWORD PTR [esi+48]
	punpcklqdq xmm5, xmm5
	pxor xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+272]
	pshufb xmm2, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+288]
	pshufb xmm4, xmm1
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+432]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm5
	pxor xmm0, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+448]
	pshufb xmm2, xmm5
	pxor xmm0, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm2, xmm1
	pxor xmm5, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+400]
	movdqa xmm2, xmm5
	pshufb xmm2, xmm4
	pxor xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+416]
	pshufb xmm5, xmm4
	pxor xmm0, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+208]
	pshufb xmm4, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+224]
	pshufb xmm5, xmm1
	pxor xmm4, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+176]
	pshufb xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+368]
	movdqa xmm3, xmm4
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+384]
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+304]
	movdqa xmm5, xmm2
	pshufb xmm5, xmm1
	pxor xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+320]
	movdqa xmm4, xmm2
	pshufb xmm4, xmm1
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+336]
	movdqa xmm3, xmm2
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+352]
	pshufb xmm2, xmm1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	sub ecx, 1
	je 221f
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movq xmm0, QWORD PTR [esi+64]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm1, QWORD PTR [esi+64]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm2
	psrlq xmm1, 32
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	pslld xmm3, 1
	por xmm3, xmm0
	psllq xmm3, 32
	pxor xmm2, xmm3
	pxor xmm2, xmm1
	movq xmm4, QWORD PTR [esi+96]
	punpcklqdq xmm4, xmm4
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [edi+560]
	movq xmm6, QWORD PTR [esi+56]
	punpcklqdq xmm6, xmm6
	pxor xmm5, xmm6
	movdqa xmm4, xmm7
	pand xmm4, xmm5
	psrld xmm5, 4
	pand xmm5, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm4
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm4, xmm0
	pand xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+128]
	pshufb xmm1, xmm5
	pxor xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movq xmm0, QWORD PTR [esi+80]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm2
	psrld xmm0, 31
	movq xmm3, QWORD PTR [esi+80]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm2
	psrlq xmm3, 32
	movq xmm4, QWORD PTR [esi+80]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm2
	pslld xmm4, 1
	por xmm4, xmm0
	psllq xmm4, 32
	pxor xmm2, xmm4
	pxor xmm2, xmm3
	movdqa xmm5, xmm7
	pand xmm5, xmm2
	psrld xmm2, 4
	pand xmm2, xmm7
	movq xmm1, QWORD PTR [esi+72]
	punpcklqdq xmm1, xmm1
	pand xmm1, xmm6
	psrld xmm1, 31
	movq xmm0, QWORD PTR [esi+72]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm6
	psrlq xmm0, 32
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	pslld xmm3, 1
	por xmm3, xmm1
	psllq xmm3, 32
	pxor xmm6, xmm3
	pxor xmm6, xmm0
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm5
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pand xmm5, xmm4
	pand xmm4, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+64]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movq xmm2, QWORD PTR [esi+104]
	punpcklqdq xmm2, xmm2
	pxor xmm6, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+80]
	pshufb xmm3, xmm5
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+96]
	pshufb xmm5, xmm4
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm4, QWORD PTR [esi+112]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+512], xmm1
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movq xmm3, QWORD PTR [esi+88]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm6
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm6
	psrlq xmm5, 32
	movq xmm4, QWORD PTR [esi+88]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm6
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm6, xmm4
	pxor xmm6, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+112]
	pshufb xmm1, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm2, xmm3
	pand xmm3, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm3
	pxor xmm1, xmm2
	movq xmm3, QWORD PTR [esi+72]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm1
	psrld xmm3, 31
	movq xmm5, QWORD PTR [esi+72]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrlq xmm5, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm6
	psrld xmm6, 4
	pand xmm6, xmm7
	movq xmm4, QWORD PTR [esi+72]
	punpcklqdq xmm4, xmm4
	pand xmm4, xmm1
	pslld xmm4, 1
	por xmm4, xmm3
	psllq xmm4, 32
	pxor xmm1, xmm4
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm0, xmm3
	pand xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm6
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm0
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm3
	pxor xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [edi+544]
	movq xmm4, QWORD PTR [esi+104]
	punpcklqdq xmm4, xmm4
	pxor xmm1, xmm4
	movq xmm5, QWORD PTR [esi+88]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm1
	psrld xmm5, 31
	movq xmm6, QWORD PTR [esi+120]
	punpcklqdq xmm6, xmm6
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqa xmm0, xmm7
	pand xmm0, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm4, XMMWORD PTR [ebx+112]
	pshufb xmm4, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+128]
	pshufb xmm2, xmm3
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm0
	pxor xmm4, xmm3
	movq xmm0, QWORD PTR [esi+88]
	punpcklqdq xmm0, xmm0
	pand xmm0, xmm1
	psrlq xmm0, 32
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm6
	pxor xmm4, xmm2
	movq xmm6, QWORD PTR [esi+88]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm1
	pslld xmm6, 1
	por xmm6, xmm5
	psllq xmm6, 32
	pxor xmm1, xmm6
	pxor xmm1, xmm0
	movq xmm5, QWORD PTR [esi+64]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrld xmm5, 31
	movq xmm3, QWORD PTR [esi+64]
	punpcklqdq xmm3, xmm3
	pand xmm3, xmm4
	psrlq xmm3, 32
	movq xmm2, QWORD PTR [esi+64]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	pslld xmm2, 1
	por xmm2, xmm5
	psllq xmm2, 32
	movdqa xmm0, xmm7
	pand xmm0, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	pxor xmm4, xmm2
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+48]
	pshufb xmm3, xmm0
	movq xmm5, QWORD PTR [esi+96]
	punpcklqdq xmm5, xmm5
	pxor xmm4, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+32]
	pand xmm0, xmm6
	pand xmm6, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+64]
	pshufb xmm5, xmm1
	pxor xmm3, xmm5
	movdqu xmm2, XMMWORD PTR [ebx+80]
	pshufb xmm2, xmm0
	pxor xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ebx+96]
	pshufb xmm0, xmm6
	pxor xmm3, xmm0
	movq xmm1, QWORD PTR [esi+120]
	punpcklqdq xmm1, xmm1
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+528], xmm3
	movq xmm2, QWORD PTR [esi+80]
	punpcklqdq xmm2, xmm2
	pand xmm2, xmm4
	psrld xmm2, 31
	movq xmm5, QWORD PTR [esi+80]
	punpcklqdq xmm5, xmm5
	pand xmm5, xmm4
	psrlq xmm5, 32
	movq xmm6, QWORD PTR [esi+80]
	punpcklqdq xmm6, xmm6
	pand xmm6, xmm4
	pslld xmm6, 1
	por xmm6, xmm2
	psllq xmm6, 32
	pxor xmm4, xmm6
	pxor xmm4, xmm5
	movdqa xmm0, xmm7
	pand xmm0, xmm4
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+48]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+32]
	pand xmm0, xmm2
	pand xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm4
	pxor xmm1, xmm3
	movdqu xmm5, XMMWORD PTR [ebx+80]
	pshufb xmm5, xmm0
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm1, xmm6
	movq xmm0, QWORD PTR [esi+112]
	punpcklqdq xmm0, xmm0
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	add esi, 112
	test ecx, ecx
	jmp 222f
221:
222:
	jne 220b
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm7
	pand xmm1, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+112]
	pshufb xmm2, xmm1
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pand xmm1, xmm3
	pand xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm0
	pxor xmm2, xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm3
	pxor xmm2, xmm6
	movdqu xmm0, XMMWORD PTR [edi+528]
	movq xmm1, QWORD PTR [esi+56]
	punpcklqdq xmm1, xmm1
	pxor xmm0, xmm1
	movdqu xmm3, XMMWORD PTR [edi+544]
	movdqa xmm4, xmm7
	pand xmm4, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [ebx+112]
	pshufb xmm5, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm4, xmm1
	pand xmm1, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm0
	pxor xmm5, xmm6
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm4, xmm1
	pxor xmm5, xmm4
	movdqa xmm1, xmm7
	pand xmm1, xmm3
	psrld xmm3, 4
	pand xmm3, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [ebx+32]
	pand xmm1, xmm0
	pand xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm3
	pxor xmm6, xmm4
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm3, xmm1
	pxor xmm6, xmm3
	movdqu xmm1, XMMWORD PTR [ebx+160]
	pshufb xmm1, xmm0
	pxor xmm6, xmm1
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm4, xmm5
	punpcklqdq xmm4, xmm2
	punpckhqdq xmm5, xmm2
	movq xmm2, QWORD PTR [esi+56]
	punpcklqdq xmm2, xmm2
	pxor xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm2
	pshufb xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [esi+64]
	pxor xmm4, xmm2
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+576], xmm4
	movdqu XMMWORD PTR [edi+592], xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm2
	movdqu xmm1, XMMWORD PTR [ebx+32]
	pand xmm2, xmm1
	pand xmm1, xmm0
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pshufb xmm5, xmm0
	pxor xmm3, xmm5
	movdqu xmm0, XMMWORD PTR [ebx+144]
	pshufb xmm0, xmm2
	pxor xmm3, xmm0
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pshufb xmm2, xmm1
	pxor xmm3, xmm2
	movdqa xmm4, xmm3
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+16]
	pshufb xmm4, xmm6
	pshufb xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm4, xmm6
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+608], xmm4
	movdqu XMMWORD PTR [edi+624], xmm3
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	jne 219b
	jmp 218f
217:
218:
	mov ebx, DWORD PTR [edi+816]
	mov esi, DWORD PTR [edi+820]
	mov ebp, DWORD PTR [edi+828]
	mov edi, DWORD PTR [edi+824]
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
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	mov DWORD PTR [esp+872], ecx
	mov DWORD PTR [esp+876], ecx
	lea esp, [esp+884]
	lea esp, [esp-888]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+884], ecx
	lea esp, [esp+888]
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

vg_camellia_ecb_decrypt:
	lea esp, [esp-1572]
	mov eax, DWORD PTR [esp+1576]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_SSE2}
	pop ecx
	mov DWORD PTR [edi+416], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	mov esi, edi
	add esi, 960
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm6, XMMWORD PTR [ebx+128]
	cmp ecx, 18
	je 20f
	mov ecx, 30
	add eax, 256
	jmp 21f
20:
	mov ecx, 22
	add eax, 192
21:
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	add eax, 8
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub eax, 16
22:
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	sub eax, 8
	sub ecx, 1
	jne 22b
	sub eax, 8
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	add eax, 8
	movq xmm0, QWORD PTR [eax]
	movdqa xmm1, xmm0
	pand xmm0, xmm7
	psrld xmm1, 8
	pand xmm1, xmm7
	punpcklwd xmm0, xmm1
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [esi], xmm0
	add esi, 16
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1524], eax
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 16
	jb 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+956], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [edi+832]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [edi+836]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [edi+856]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [edi+860]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [edi+864]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [edi+868]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [edi+872]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [edi+876]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [edi+880]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [edi+884]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [edi+888]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [edi+892]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [edi+896]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [edi+900]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [edi+904]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [edi+908]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [edi+912]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [edi+916]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [edi+920]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [edi+924]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [edi+936]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [edi+940]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [edi+944]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [edi+948]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [edi+952]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [edi+956]
	mov DWORD PTR [esi+252], eax
	add esi, 256
	sub ebp, 16
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 16
	jae 25b
	jmp 24f
23:
24:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 8
	jb 26f
28:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+828], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 8
	jae 28b
	jmp 27f
26:
27:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 4
	jb 29f
211:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+764], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 4
	jae 211b
	jmp 210f
29:
210:
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 2
	jb 212f
214:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+732], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	cmp ebp, 2
	jae 214b
	jmp 213f
212:
213:
	mov eax, DWORD PTR [edi+1524]
	test eax, eax
	je 215f
217:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+716], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jne 217b
	jmp 216f
215:
216:
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
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
	movdqu XMMWORD PTR [esp+744], xmm0
	movdqu XMMWORD PTR [esp+760], xmm0
	movdqu XMMWORD PTR [esp+776], xmm0
	movdqu XMMWORD PTR [esp+792], xmm0
	movdqu XMMWORD PTR [esp+808], xmm0
	movdqu XMMWORD PTR [esp+824], xmm0
	movdqu XMMWORD PTR [esp+840], xmm0
	movdqu XMMWORD PTR [esp+856], xmm0
	movdqu XMMWORD PTR [esp+872], xmm0
	movdqu XMMWORD PTR [esp+888], xmm0
	movdqu XMMWORD PTR [esp+904], xmm0
	movdqu XMMWORD PTR [esp+920], xmm0
	movdqu XMMWORD PTR [esp+936], xmm0
	movdqu XMMWORD PTR [esp+952], xmm0
	movdqu XMMWORD PTR [esp+968], xmm0
	movdqu XMMWORD PTR [esp+984], xmm0
	movdqu XMMWORD PTR [esp+1000], xmm0
	movdqu XMMWORD PTR [esp+1016], xmm0
	movdqu XMMWORD PTR [esp+1032], xmm0
	movdqu XMMWORD PTR [esp+1048], xmm0
	movdqu XMMWORD PTR [esp+1064], xmm0
	movdqu XMMWORD PTR [esp+1080], xmm0
	movdqu XMMWORD PTR [esp+1096], xmm0
	movdqu XMMWORD PTR [esp+1112], xmm0
	movdqu XMMWORD PTR [esp+1128], xmm0
	movdqu XMMWORD PTR [esp+1144], xmm0
	movdqu XMMWORD PTR [esp+1160], xmm0
	movdqu XMMWORD PTR [esp+1176], xmm0
	movdqu XMMWORD PTR [esp+1192], xmm0
	movdqu XMMWORD PTR [esp+1208], xmm0
	movdqu XMMWORD PTR [esp+1224], xmm0
	movdqu XMMWORD PTR [esp+1240], xmm0
	movdqu XMMWORD PTR [esp+1256], xmm0
	movdqu XMMWORD PTR [esp+1272], xmm0
	movdqu XMMWORD PTR [esp+1288], xmm0
	movdqu XMMWORD PTR [esp+1304], xmm0
	movdqu XMMWORD PTR [esp+1320], xmm0
	movdqu XMMWORD PTR [esp+1336], xmm0
	movdqu XMMWORD PTR [esp+1352], xmm0
	movdqu XMMWORD PTR [esp+1368], xmm0
	movdqu XMMWORD PTR [esp+1384], xmm0
	movdqu XMMWORD PTR [esp+1400], xmm0
	movdqu XMMWORD PTR [esp+1416], xmm0
	movdqu XMMWORD PTR [esp+1432], xmm0
	movdqu XMMWORD PTR [esp+1448], xmm0
	movdqu XMMWORD PTR [esp+1464], xmm0
	movdqu XMMWORD PTR [esp+1480], xmm0
	movdqu XMMWORD PTR [esp+1496], xmm0
	movdqu XMMWORD PTR [esp+1512], xmm0
	movdqu XMMWORD PTR [esp+1528], xmm0
	movdqu XMMWORD PTR [esp+1544], xmm0
	mov DWORD PTR [esp+1560], ecx
	mov DWORD PTR [esp+1564], ecx
	lea esp, [esp+1572]
	lea esp, [esp-1576]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+1572], ecx
	lea esp, [esp+1576]
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
