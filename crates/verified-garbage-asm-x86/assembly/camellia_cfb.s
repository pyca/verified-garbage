// The functions of `src/camellia_cfb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_cfb128_encrypt_aesni:
	lea esp, [esp-576]
	mov eax, DWORD PTR [esp+580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+504], ebx
	mov DWORD PTR [eax+508], esi
	mov DWORD PTR [eax+512], edi
	mov DWORD PTR [eax+516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+540], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+524], eax
	test eax, eax
	je 23f
25:
	mov esi, DWORD PTR [edi+520]
	mov ebp, DWORD PTR [edi+524]
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm0, XMMWORD PTR [edi+8]
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
26:
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	movq xmm5, QWORD PTR [esi+16]
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
	movq xmm5, QWORD PTR [esi+24]
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
	movq xmm5, QWORD PTR [esi+32]
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
	movq xmm5, QWORD PTR [esi+40]
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
	sub ecx, 1
	je 27f
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
	movdqu xmm2, XMMWORD PTR [esi+64]
	pand xmm2, xmm4
	movdqa xmm3, xmm2
	movdqa xmm5, xmm2
	pslld xmm5, 1
	psrld xmm2, 31
	por xmm5, xmm2
	psllq xmm5, 32
	psrlq xmm3, 32
	pxor xmm4, xmm5
	pxor xmm4, xmm3
	movdqu xmm2, XMMWORD PTR [esi+96]
	pxor xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [esi+80]
	pand xmm2, xmm4
	movdqa xmm3, xmm2
	movdqa xmm5, xmm2
	pslld xmm5, 1
	psrld xmm2, 31
	por xmm5, xmm2
	psllq xmm5, 32
	psrlq xmm3, 32
	pxor xmm4, xmm5
	pxor xmm4, xmm3
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm2, xmm5
	pand xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [esi+112]
	pxor xmm3, xmm5
	pxor xmm2, xmm2
	pshufd xmm1, xmm3, 78
	punpcklqdq xmm1, xmm2
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm2
	add esi, 112
	test ecx, ecx
	jmp 28f
27:
28:
	jne 26b
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	pshufd xmm3, xmm1, 78
	pxor xmm3, xmm1
	punpcklqdq xmm2, xmm3
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm3, xmm4
	pand xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+160]
	pshufb xmm5, xmm3
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [esi+64]
	pxor xmm6, xmm5
	movdqu XMMWORD PTR [edi+8], xmm6
	mov esi, DWORD PTR [edi+520]
	mov ebp, DWORD PTR [edi+524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+540], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+520], esi
	mov DWORD PTR [edi+524], ebp
	jne 25b
	jmp 24f
23:
24:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+504]
	mov esi, DWORD PTR [edi+508]
	mov ebp, DWORD PTR [edi+516]
	mov edi, DWORD PTR [edi+512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	lea esp, [esp+576]
	lea esp, [esp-580]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+576], ecx
	lea esp, [esp+580]
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

vg_camellia_cfb128_encrypt:
	lea esp, [esp-1576]
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1524], eax
	test eax, eax
	je 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jne 25b
	jmp 24f
23:
24:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	movdqu XMMWORD PTR [esp+1436], xmm0
	movdqu XMMWORD PTR [esp+1452], xmm0
	movdqu XMMWORD PTR [esp+1468], xmm0
	movdqu XMMWORD PTR [esp+1484], xmm0
	movdqu XMMWORD PTR [esp+1500], xmm0
	movdqu XMMWORD PTR [esp+1516], xmm0
	movdqu XMMWORD PTR [esp+1532], xmm0
	movdqu XMMWORD PTR [esp+1548], xmm0
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	lea esp, [esp+1576]
	lea esp, [esp-1580]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+1576], ecx
	lea esp, [esp+1580]
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

vg_camellia_cfb128_decrypt_aesni:
	lea esp, [esp-888]
	mov eax, DWORD PTR [esp+892]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+896]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+900]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+904]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+908]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+816], ebx
	mov DWORD PTR [eax+820], esi
	mov DWORD PTR [eax+824], edi
	mov DWORD PTR [eax+828], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+852], eax
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+836], eax
	test eax, eax
	mov eax, DWORD PTR [edi+836]
	cmp eax, 4
	jb 23f
25:
	mov esi, DWORD PTR [edi+832]
	mov ebp, DWORD PTR [edi+836]
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+852], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+592]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+596]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+600]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+604]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+636]
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
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+852], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+592]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+596]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+600]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+604]
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
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+576], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+580], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+584], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+588], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+852], eax
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+576]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+580]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+584]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+588]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+832], esi
	mov DWORD PTR [edi+836], ebp
	jne 217b
	jmp 216f
215:
216:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+816]
	mov esi, DWORD PTR [edi+820]
	mov ebp, DWORD PTR [edi+828]
	mov edi, DWORD PTR [edi+824]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	mov DWORD PTR [esp+876], ecx
	mov DWORD PTR [esp+880], ecx
	lea esp, [esp+888]
	lea esp, [esp-892]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+888], ecx
	lea esp, [esp+892]
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

vg_camellia_cfb128_decrypt:
	lea esp, [esp-1576]
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1524], eax
	test eax, eax
	mov eax, DWORD PTR [edi+1524]
	cmp eax, 16
	jb 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+832], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+836], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+856], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+860], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+864], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+868], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+872], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+876], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+880], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+884], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+888], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+892], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+896], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+900], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+904], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+908], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+912], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+916], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+920], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+924], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+928], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+932], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+936], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+940], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+944], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+948], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+952], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+956], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+1540], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+828]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [esi+128]
	xor eax, DWORD PTR [edi+832]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [esi+132]
	xor eax, DWORD PTR [edi+836]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [esi+136]
	xor eax, DWORD PTR [edi+840]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [esi+140]
	xor eax, DWORD PTR [edi+844]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [esi+144]
	xor eax, DWORD PTR [edi+848]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [esi+148]
	xor eax, DWORD PTR [edi+852]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [esi+152]
	xor eax, DWORD PTR [edi+856]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [esi+156]
	xor eax, DWORD PTR [edi+860]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [esi+160]
	xor eax, DWORD PTR [edi+864]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [esi+164]
	xor eax, DWORD PTR [edi+868]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [esi+168]
	xor eax, DWORD PTR [edi+872]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [esi+172]
	xor eax, DWORD PTR [edi+876]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [esi+176]
	xor eax, DWORD PTR [edi+880]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [esi+180]
	xor eax, DWORD PTR [edi+884]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [esi+184]
	xor eax, DWORD PTR [edi+888]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [esi+188]
	xor eax, DWORD PTR [edi+892]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [esi+192]
	xor eax, DWORD PTR [edi+896]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [esi+196]
	xor eax, DWORD PTR [edi+900]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [esi+200]
	xor eax, DWORD PTR [edi+904]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [esi+204]
	xor eax, DWORD PTR [edi+908]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [esi+208]
	xor eax, DWORD PTR [edi+912]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [esi+212]
	xor eax, DWORD PTR [edi+916]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [esi+216]
	xor eax, DWORD PTR [edi+920]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [esi+220]
	xor eax, DWORD PTR [edi+924]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [esi+224]
	xor eax, DWORD PTR [edi+928]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [esi+228]
	xor eax, DWORD PTR [edi+932]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [esi+232]
	xor eax, DWORD PTR [edi+936]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [esi+236]
	xor eax, DWORD PTR [edi+940]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [esi+240]
	xor eax, DWORD PTR [edi+944]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [esi+244]
	xor eax, DWORD PTR [edi+948]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [esi+248]
	xor eax, DWORD PTR [edi+952]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [esi+252]
	xor eax, DWORD PTR [edi+956]
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
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+768], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+772], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+776], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+780], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+784], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+788], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+792], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+796], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+800], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+804], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+808], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+812], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+816], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+820], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+824], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+828], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1540], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+764]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [esi+64]
	xor eax, DWORD PTR [edi+768]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [esi+68]
	xor eax, DWORD PTR [edi+772]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [esi+72]
	xor eax, DWORD PTR [edi+776]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [esi+76]
	xor eax, DWORD PTR [edi+780]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [esi+80]
	xor eax, DWORD PTR [edi+784]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [esi+84]
	xor eax, DWORD PTR [edi+788]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [esi+88]
	xor eax, DWORD PTR [edi+792]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [esi+92]
	xor eax, DWORD PTR [edi+796]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [esi+96]
	xor eax, DWORD PTR [edi+800]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [esi+100]
	xor eax, DWORD PTR [edi+804]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [esi+104]
	xor eax, DWORD PTR [edi+808]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [esi+108]
	xor eax, DWORD PTR [edi+812]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [esi+112]
	xor eax, DWORD PTR [edi+816]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [esi+116]
	xor eax, DWORD PTR [edi+820]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [esi+120]
	xor eax, DWORD PTR [edi+824]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [esi+124]
	xor eax, DWORD PTR [edi+828]
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
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+736], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+740], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+744], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+748], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+752], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+756], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+760], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+764], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1540], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [esi+32]
	xor eax, DWORD PTR [edi+736]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [esi+36]
	xor eax, DWORD PTR [edi+740]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [esi+40]
	xor eax, DWORD PTR [edi+744]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [esi+44]
	xor eax, DWORD PTR [edi+748]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [esi+48]
	xor eax, DWORD PTR [edi+752]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [esi+52]
	xor eax, DWORD PTR [edi+756]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [esi+56]
	xor eax, DWORD PTR [edi+760]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [esi+60]
	xor eax, DWORD PTR [edi+764]
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
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+720], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+724], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+728], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+732], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1540], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi+16]
	xor eax, DWORD PTR [edi+720]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [esi+20]
	xor eax, DWORD PTR [edi+724]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [esi+24]
	xor eax, DWORD PTR [edi+728]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [esi+28]
	xor eax, DWORD PTR [edi+732]
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
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [edi+716], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	mov ebx, DWORD PTR [edi+416]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 960
	call {vg_camellia_crypt16_sse2}
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jne 217b
	jmp 216f
215:
216:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	movdqu XMMWORD PTR [esp+1436], xmm0
	movdqu XMMWORD PTR [esp+1452], xmm0
	movdqu XMMWORD PTR [esp+1468], xmm0
	movdqu XMMWORD PTR [esp+1484], xmm0
	movdqu XMMWORD PTR [esp+1500], xmm0
	movdqu XMMWORD PTR [esp+1516], xmm0
	movdqu XMMWORD PTR [esp+1532], xmm0
	movdqu XMMWORD PTR [esp+1548], xmm0
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	lea esp, [esp+1576]
	lea esp, [esp-1580]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+1576], ecx
	lea esp, [esp+1580]
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

vg_camellia_cfb128_encrypt_final_aesni:
	lea esp, [esp-576]
	mov eax, DWORD PTR [esp+580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+504], ebx
	mov DWORD PTR [eax+508], esi
	mov DWORD PTR [eax+512], edi
	mov DWORD PTR [eax+516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+540], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+524], eax
	test eax, eax
	je 23f
25:
	mov esi, DWORD PTR [edi+520]
	mov ebp, DWORD PTR [edi+524]
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm0, XMMWORD PTR [edi+8]
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
26:
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	movq xmm5, QWORD PTR [esi+16]
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
	movq xmm5, QWORD PTR [esi+24]
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
	movq xmm5, QWORD PTR [esi+32]
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
	movq xmm5, QWORD PTR [esi+40]
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
	sub ecx, 1
	je 27f
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
	movdqu xmm2, XMMWORD PTR [esi+64]
	pand xmm2, xmm4
	movdqa xmm3, xmm2
	movdqa xmm5, xmm2
	pslld xmm5, 1
	psrld xmm2, 31
	por xmm5, xmm2
	psllq xmm5, 32
	psrlq xmm3, 32
	pxor xmm4, xmm5
	pxor xmm4, xmm3
	movdqu xmm2, XMMWORD PTR [esi+96]
	pxor xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [esi+80]
	pand xmm2, xmm4
	movdqa xmm3, xmm2
	movdqa xmm5, xmm2
	pslld xmm5, 1
	psrld xmm2, 31
	por xmm5, xmm2
	psllq xmm5, 32
	psrlq xmm3, 32
	pxor xmm4, xmm5
	pxor xmm4, xmm3
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm2, xmm5
	pand xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [esi+112]
	pxor xmm3, xmm5
	pxor xmm2, xmm2
	pshufd xmm1, xmm3, 78
	punpcklqdq xmm1, xmm2
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm2
	add esi, 112
	test ecx, ecx
	jmp 28f
27:
28:
	jne 26b
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	pshufd xmm3, xmm1, 78
	pxor xmm3, xmm1
	punpcklqdq xmm2, xmm3
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm3, xmm4
	pand xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+160]
	pshufb xmm5, xmm3
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [esi+64]
	pxor xmm6, xmm5
	movdqu XMMWORD PTR [edi+8], xmm6
	mov esi, DWORD PTR [edi+520]
	mov ebp, DWORD PTR [edi+524]
	cmp ebp, 16
	jb 29f
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+540], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+520], esi
	mov DWORD PTR [edi+524], ebp
	jmp 210f
29:
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+540], eax
	mov ebx, edi
	add ebx, 8
211:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 211b
	mov DWORD PTR [edi+520], esi
	mov DWORD PTR [edi+524], ebp
210:
	jne 25b
	jmp 24f
23:
24:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+504]
	mov esi, DWORD PTR [edi+508]
	mov ebp, DWORD PTR [edi+516]
	mov edi, DWORD PTR [edi+512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	lea esp, [esp+576]
	lea esp, [esp-580]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+576], ecx
	lea esp, [esp+580]
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

vg_camellia_cfb128_encrypt_final:
	lea esp, [esp-1576]
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1524], eax
	test eax, eax
	je 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
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
	cmp ebp, 16
	jb 26f
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jmp 27f
26:
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+1540], eax
	mov ebx, edi
	add ebx, 704
28:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 28b
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
27:
	jne 25b
	jmp 24f
23:
24:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	movdqu XMMWORD PTR [esp+1436], xmm0
	movdqu XMMWORD PTR [esp+1452], xmm0
	movdqu XMMWORD PTR [esp+1468], xmm0
	movdqu XMMWORD PTR [esp+1484], xmm0
	movdqu XMMWORD PTR [esp+1500], xmm0
	movdqu XMMWORD PTR [esp+1516], xmm0
	movdqu XMMWORD PTR [esp+1532], xmm0
	movdqu XMMWORD PTR [esp+1548], xmm0
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	lea esp, [esp+1576]
	lea esp, [esp-1580]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+1576], ecx
	lea esp, [esp+1580]
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

vg_camellia_cfb128_decrypt_final_aesni:
	lea esp, [esp-576]
	mov eax, DWORD PTR [esp+580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+504], ebx
	mov DWORD PTR [eax+508], esi
	mov DWORD PTR [eax+512], edi
	mov DWORD PTR [eax+516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+540], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_CAMELLIA_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+524], eax
	test eax, eax
	je 23f
25:
	mov esi, DWORD PTR [edi+520]
	mov ebp, DWORD PTR [edi+524]
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [edi+8], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [edi+12], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [edi+20], eax
	mov ebx, DWORD PTR [edi]
	mov ecx, DWORD PTR [esp+8]
	shr ecx, 3
	add ecx, 1
	mov esi, edi
	add esi, 24
	movdqu xmm0, XMMWORD PTR [edi+8]
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
26:
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	movq xmm5, QWORD PTR [esi+16]
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
	movq xmm5, QWORD PTR [esi+24]
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
	movq xmm5, QWORD PTR [esi+32]
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
	movq xmm5, QWORD PTR [esi+40]
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
	sub ecx, 1
	je 27f
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
	movdqu xmm2, XMMWORD PTR [esi+64]
	pand xmm2, xmm4
	movdqa xmm3, xmm2
	movdqa xmm5, xmm2
	pslld xmm5, 1
	psrld xmm2, 31
	por xmm5, xmm2
	psllq xmm5, 32
	psrlq xmm3, 32
	pxor xmm4, xmm5
	pxor xmm4, xmm3
	movdqu xmm2, XMMWORD PTR [esi+96]
	pxor xmm4, xmm2
	movdqu xmm2, XMMWORD PTR [esi+80]
	pand xmm2, xmm4
	movdqa xmm3, xmm2
	movdqa xmm5, xmm2
	pslld xmm5, 1
	psrld xmm2, 31
	por xmm5, xmm2
	psllq xmm5, 32
	psrlq xmm3, 32
	pxor xmm4, xmm5
	pxor xmm4, xmm3
	movdqa xmm2, xmm4
	pand xmm2, xmm7
	psrld xmm4, 4
	pand xmm4, xmm7
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm2, xmm5
	pand xmm5, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pshufb xmm6, xmm4
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pshufb xmm6, xmm2
	pxor xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pshufb xmm6, xmm5
	pxor xmm3, xmm6
	movdqu xmm5, XMMWORD PTR [esi+112]
	pxor xmm3, xmm5
	pxor xmm2, xmm2
	pshufd xmm1, xmm3, 78
	punpcklqdq xmm1, xmm2
	movdqa xmm0, xmm3
	punpcklqdq xmm0, xmm2
	add esi, 112
	test ecx, ecx
	jmp 28f
27:
28:
	jne 26b
	pshufd xmm2, xmm0, 78
	pxor xmm2, xmm0
	pshufd xmm3, xmm1, 78
	pxor xmm3, xmm1
	punpcklqdq xmm2, xmm3
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	psrld xmm2, 4
	pand xmm2, xmm7
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pshufb xmm6, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm3, xmm4
	pand xmm4, xmm2
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm2
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+160]
	pshufb xmm5, xmm3
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+176]
	pshufb xmm5, xmm4
	pxor xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+32]
	pshufb xmm6, xmm5
	movdqu xmm5, XMMWORD PTR [esi+64]
	pxor xmm6, xmm5
	movdqu XMMWORD PTR [edi+8], xmm6
	mov esi, DWORD PTR [edi+520]
	mov ebp, DWORD PTR [edi+524]
	cmp ebp, 16
	jb 29f
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+540], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+8]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+12]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+520], esi
	mov DWORD PTR [edi+524], ebp
	jmp 210f
29:
	mov eax, DWORD PTR [edi+8]
	mov DWORD PTR [edi+528], eax
	mov eax, DWORD PTR [edi+12]
	mov DWORD PTR [edi+532], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+536], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+540], eax
	mov ebx, edi
	add ebx, 8
211:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 211b
	mov DWORD PTR [edi+520], esi
	mov DWORD PTR [edi+524], ebp
210:
	jne 25b
	jmp 24f
23:
24:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+504]
	mov esi, DWORD PTR [edi+508]
	mov ebp, DWORD PTR [edi+516]
	mov edi, DWORD PTR [edi+512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	lea esp, [esp+576]
	lea esp, [esp-580]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+576], ecx
	lea esp, [esp+580]
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

vg_camellia_cfb128_decrypt_final:
	lea esp, [esp-1576]
	mov eax, DWORD PTR [esp+1580]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1584]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1588]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1592]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+1596]
	mov DWORD PTR [esp+20], eax
	mov eax, esp
	add eax, 28
	mov DWORD PTR [esp+24], eax
	mov eax, DWORD PTR [esp+24]
	mov DWORD PTR [eax+1504], ebx
	mov DWORD PTR [eax+1508], esi
	mov DWORD PTR [eax+1512], edi
	mov DWORD PTR [eax+1516], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
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
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1520], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [edi+1524], eax
	test eax, eax
	je 23f
25:
	mov esi, DWORD PTR [edi+1520]
	mov ebp, DWORD PTR [edi+1524]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [edi+712], eax
	mov eax, DWORD PTR [edi+1540]
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
	cmp ebp, 16
	jb 26f
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1540], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+712]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+716]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
	jmp 27f
26:
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+1528], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+1532], eax
	mov eax, DWORD PTR [edi+712]
	mov DWORD PTR [edi+1536], eax
	mov eax, DWORD PTR [edi+716]
	mov DWORD PTR [edi+1540], eax
	mov ebx, edi
	add ebx, 704
28:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 28b
	mov DWORD PTR [edi+1520], esi
	mov DWORD PTR [edi+1524], ebp
27:
	jne 25b
	jmp 24f
23:
24:
	mov esi, DWORD PTR [esp+12]
	mov eax, DWORD PTR [edi+1528]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1532]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1536]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1540]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1504]
	mov esi, DWORD PTR [edi+1508]
	mov ebp, DWORD PTR [edi+1516]
	mov edi, DWORD PTR [edi+1512]
	pxor xmm0, xmm0
	mov ecx, 0
	movdqu XMMWORD PTR [esp+28], xmm0
	movdqu XMMWORD PTR [esp+44], xmm0
	movdqu XMMWORD PTR [esp+60], xmm0
	movdqu XMMWORD PTR [esp+76], xmm0
	movdqu XMMWORD PTR [esp+92], xmm0
	movdqu XMMWORD PTR [esp+108], xmm0
	movdqu XMMWORD PTR [esp+124], xmm0
	movdqu XMMWORD PTR [esp+140], xmm0
	movdqu XMMWORD PTR [esp+156], xmm0
	movdqu XMMWORD PTR [esp+172], xmm0
	movdqu XMMWORD PTR [esp+188], xmm0
	movdqu XMMWORD PTR [esp+204], xmm0
	movdqu XMMWORD PTR [esp+220], xmm0
	movdqu XMMWORD PTR [esp+236], xmm0
	movdqu XMMWORD PTR [esp+252], xmm0
	movdqu XMMWORD PTR [esp+268], xmm0
	movdqu XMMWORD PTR [esp+284], xmm0
	movdqu XMMWORD PTR [esp+300], xmm0
	movdqu XMMWORD PTR [esp+316], xmm0
	movdqu XMMWORD PTR [esp+332], xmm0
	movdqu XMMWORD PTR [esp+348], xmm0
	movdqu XMMWORD PTR [esp+364], xmm0
	movdqu XMMWORD PTR [esp+380], xmm0
	movdqu XMMWORD PTR [esp+396], xmm0
	movdqu XMMWORD PTR [esp+412], xmm0
	movdqu XMMWORD PTR [esp+428], xmm0
	movdqu XMMWORD PTR [esp+444], xmm0
	movdqu XMMWORD PTR [esp+460], xmm0
	movdqu XMMWORD PTR [esp+476], xmm0
	movdqu XMMWORD PTR [esp+492], xmm0
	movdqu XMMWORD PTR [esp+508], xmm0
	movdqu XMMWORD PTR [esp+524], xmm0
	movdqu XMMWORD PTR [esp+540], xmm0
	movdqu XMMWORD PTR [esp+556], xmm0
	movdqu XMMWORD PTR [esp+572], xmm0
	movdqu XMMWORD PTR [esp+588], xmm0
	movdqu XMMWORD PTR [esp+604], xmm0
	movdqu XMMWORD PTR [esp+620], xmm0
	movdqu XMMWORD PTR [esp+636], xmm0
	movdqu XMMWORD PTR [esp+652], xmm0
	movdqu XMMWORD PTR [esp+668], xmm0
	movdqu XMMWORD PTR [esp+684], xmm0
	movdqu XMMWORD PTR [esp+700], xmm0
	movdqu XMMWORD PTR [esp+716], xmm0
	movdqu XMMWORD PTR [esp+732], xmm0
	movdqu XMMWORD PTR [esp+748], xmm0
	movdqu XMMWORD PTR [esp+764], xmm0
	movdqu XMMWORD PTR [esp+780], xmm0
	movdqu XMMWORD PTR [esp+796], xmm0
	movdqu XMMWORD PTR [esp+812], xmm0
	movdqu XMMWORD PTR [esp+828], xmm0
	movdqu XMMWORD PTR [esp+844], xmm0
	movdqu XMMWORD PTR [esp+860], xmm0
	movdqu XMMWORD PTR [esp+876], xmm0
	movdqu XMMWORD PTR [esp+892], xmm0
	movdqu XMMWORD PTR [esp+908], xmm0
	movdqu XMMWORD PTR [esp+924], xmm0
	movdqu XMMWORD PTR [esp+940], xmm0
	movdqu XMMWORD PTR [esp+956], xmm0
	movdqu XMMWORD PTR [esp+972], xmm0
	movdqu XMMWORD PTR [esp+988], xmm0
	movdqu XMMWORD PTR [esp+1004], xmm0
	movdqu XMMWORD PTR [esp+1020], xmm0
	movdqu XMMWORD PTR [esp+1036], xmm0
	movdqu XMMWORD PTR [esp+1052], xmm0
	movdqu XMMWORD PTR [esp+1068], xmm0
	movdqu XMMWORD PTR [esp+1084], xmm0
	movdqu XMMWORD PTR [esp+1100], xmm0
	movdqu XMMWORD PTR [esp+1116], xmm0
	movdqu XMMWORD PTR [esp+1132], xmm0
	movdqu XMMWORD PTR [esp+1148], xmm0
	movdqu XMMWORD PTR [esp+1164], xmm0
	movdqu XMMWORD PTR [esp+1180], xmm0
	movdqu XMMWORD PTR [esp+1196], xmm0
	movdqu XMMWORD PTR [esp+1212], xmm0
	movdqu XMMWORD PTR [esp+1228], xmm0
	movdqu XMMWORD PTR [esp+1244], xmm0
	movdqu XMMWORD PTR [esp+1260], xmm0
	movdqu XMMWORD PTR [esp+1276], xmm0
	movdqu XMMWORD PTR [esp+1292], xmm0
	movdqu XMMWORD PTR [esp+1308], xmm0
	movdqu XMMWORD PTR [esp+1324], xmm0
	movdqu XMMWORD PTR [esp+1340], xmm0
	movdqu XMMWORD PTR [esp+1356], xmm0
	movdqu XMMWORD PTR [esp+1372], xmm0
	movdqu XMMWORD PTR [esp+1388], xmm0
	movdqu XMMWORD PTR [esp+1404], xmm0
	movdqu XMMWORD PTR [esp+1420], xmm0
	movdqu XMMWORD PTR [esp+1436], xmm0
	movdqu XMMWORD PTR [esp+1452], xmm0
	movdqu XMMWORD PTR [esp+1468], xmm0
	movdqu XMMWORD PTR [esp+1484], xmm0
	movdqu XMMWORD PTR [esp+1500], xmm0
	movdqu XMMWORD PTR [esp+1516], xmm0
	movdqu XMMWORD PTR [esp+1532], xmm0
	movdqu XMMWORD PTR [esp+1548], xmm0
	mov DWORD PTR [esp+1564], ecx
	mov DWORD PTR [esp+1568], ecx
	lea esp, [esp+1576]
	lea esp, [esp-1580]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+1576], ecx
	lea esp, [esp+1580]
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
