// The functions of `src/seed_cbc.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cbc_encrypt_chained_aesni:
	lea esp, [esp-676]
	mov eax, DWORD PTR [esp+680]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+684]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+688]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+692]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+608], ebx
	mov DWORD PTR [eax+612], esi
	mov DWORD PTR [eax+616], edi
	mov DWORD PTR [eax+620], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+644], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 96
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	add esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+628], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+624]
	mov ebp, DWORD PTR [edi+628]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+644]
	mov DWORD PTR [edi+28], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm0, XMMWORD PTR [edi+16]
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm0, xmm4
	pshufd xmm1, xmm0, 0
	movdqu XMMWORD PTR [edi+32], xmm1
	pshufd xmm1, xmm0, 85
	movdqu XMMWORD PTR [edi+48], xmm1
	pshufd xmm5, xmm0, 170
	pshufd xmm0, xmm0, 255
24:
	movdqu XMMWORD PTR [edi+64], xmm5
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm6, xmm0
	paddd xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	paddd xmm0, xmm6
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm6, xmm0
	paddd xmm0, xmm5
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	paddd xmm0, xmm6
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm0, xmm7
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+32]
	pshufb xmm3, xmm1
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+144]
	pshufb xmm2, xmm3
	aesenclast xmm2, xmm7
	movdqa xmm1, xmm2
	psrld xmm1, 4
	pand xmm1, xmm7
	pand xmm2, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+64]
	pshufb xmm3, xmm1
	pxor xmm0, xmm3
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+96]
	pshufb xmm3, xmm1
	pxor xmm4, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	pshufd xmm1, xmm0, 57
	pshufd xmm2, xmm0, 78
	pshufd xmm3, xmm0, 147
	pxor xmm0, xmm1
	pxor xmm2, xmm3
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+80]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	punpcklqdq xmm5, xmm0
	pshufd xmm5, xmm5, 136
	movdqu xmm1, XMMWORD PTR [edi+32]
	movdqu xmm2, XMMWORD PTR [edi+48]
	punpcklqdq xmm1, xmm2
	pshufd xmm1, xmm1, 136
	punpcklqdq xmm5, xmm1
	movdqu xmm4, XMMWORD PTR [ebx+160]
	pshufb xmm5, xmm4
	movdqu XMMWORD PTR [edi+16], xmm5
	mov esi, DWORD PTR [edi+624]
	mov ebp, DWORD PTR [edi+628]
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+624], esi
	mov DWORD PTR [edi+628], ebp
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+608]
	mov esi, DWORD PTR [edi+612]
	mov ebp, DWORD PTR [edi+620]
	mov edi, DWORD PTR [edi+616]
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
	mov DWORD PTR [esp+664], ecx
	mov DWORD PTR [esp+668], ecx
	lea esp, [esp+676]
	lea esp, [esp-680]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+676], ecx
	lea esp, [esp+680]
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

vg_seed_cbc_encrypt_chained:
	lea esp, [esp-1860]
	mov eax, DWORD PTR [esp+1864]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1868]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1872]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1876]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1792], ebx
	mov DWORD PTR [eax+1796], esi
	mov DWORD PTR [eax+1800], edi
	mov DWORD PTR [eax+1804], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_SSE2}
	pop ecx
	mov DWORD PTR [edi+480], eax
	movdqu xmm0, XMMWORD PTR [eax]
	mov eax, DWORD PTR [esp+4]
	add eax, 0
	mov esi, edi
	add esi, 1280
	mov ecx, 16
20:
	movq xmm0, QWORD PTR [eax]
	pshufd xmm1, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm1
	pshufd xmm1, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm1
	add eax, 8
	add esi, 32
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1812], eax
	test eax, eax
	je 21f
23:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	jne 23b
	jmp 22f
21:
22:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1824]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1828]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1792]
	mov esi, DWORD PTR [edi+1796]
	mov ebp, DWORD PTR [edi+1804]
	mov edi, DWORD PTR [edi+1800]
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
	movdqu XMMWORD PTR [esp+1560], xmm0
	movdqu XMMWORD PTR [esp+1576], xmm0
	movdqu XMMWORD PTR [esp+1592], xmm0
	movdqu XMMWORD PTR [esp+1608], xmm0
	movdqu XMMWORD PTR [esp+1624], xmm0
	movdqu XMMWORD PTR [esp+1640], xmm0
	movdqu XMMWORD PTR [esp+1656], xmm0
	movdqu XMMWORD PTR [esp+1672], xmm0
	movdqu XMMWORD PTR [esp+1688], xmm0
	movdqu XMMWORD PTR [esp+1704], xmm0
	movdqu XMMWORD PTR [esp+1720], xmm0
	movdqu XMMWORD PTR [esp+1736], xmm0
	movdqu XMMWORD PTR [esp+1752], xmm0
	movdqu XMMWORD PTR [esp+1768], xmm0
	movdqu XMMWORD PTR [esp+1784], xmm0
	movdqu XMMWORD PTR [esp+1800], xmm0
	movdqu XMMWORD PTR [esp+1816], xmm0
	movdqu XMMWORD PTR [esp+1832], xmm0
	mov DWORD PTR [esp+1848], ecx
	mov DWORD PTR [esp+1852], ecx
	lea esp, [esp+1860]
	lea esp, [esp-1868]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+1864], ecx
	lea esp, [esp+1868]
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

vg_seed_cbc_decrypt_chained_aesni:
	lea esp, [esp-740]
	mov eax, DWORD PTR [esp+744]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+748]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+752]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+756]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+672], ebx
	mov DWORD PTR [eax+676], esi
	mov DWORD PTR [eax+680], edi
	mov DWORD PTR [eax+684], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+708], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_AESNI_WIDE}
	pop ecx
	mov DWORD PTR [edi], eax
	mov ebx, eax
	mov eax, DWORD PTR [esp+4]
	mov esi, edi
	add esi, 544
	mov ecx, 8
20:
	movdqu xmm0, XMMWORD PTR [eax]
	pshufd xmm4, xmm0, 170
	movdqu XMMWORD PTR [esi], xmm4
	pshufd xmm4, xmm0, 255
	movdqu XMMWORD PTR [esi+16], xmm4
	pshufd xmm4, xmm0, 0
	movdqu XMMWORD PTR [esi+32], xmm4
	pshufd xmm4, xmm0, 85
	movdqu XMMWORD PTR [esi+48], xmm4
	add eax, 16
	sub esi, 64
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+688], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+692], eax
	test eax, eax
	mov eax, DWORD PTR [edi+692]
	cmp eax, 4
	jb 21f
23:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+668], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
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
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
24:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 24b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
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
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+612]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+616]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+620]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+628]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+632]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+636]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+640]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+644]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [edi+648]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+648], eax
	mov eax, DWORD PTR [edi+652]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+652], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+644]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+648]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+652]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+656]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+656], eax
	mov eax, DWORD PTR [edi+660]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+660], eax
	mov eax, DWORD PTR [edi+664]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+664], eax
	mov eax, DWORD PTR [edi+668]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+668], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+656]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+660]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+664]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+668]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 4
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+692]
	cmp eax, 2
	jb 25f
27:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+636], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
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
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
28:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 28b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
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
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+612]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+616]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+620]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+624]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+628]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+632]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+636]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+624]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+628]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	cmp ebp, 2
	jae 27b
	jmp 26f
25:
26:
	mov eax, DWORD PTR [edi+692]
	test eax, eax
	je 29f
211:
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+620], eax
	mov ebx, DWORD PTR [edi]
	mov esi, edi
	add esi, 96
	mov eax, 8
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm4, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+608]
	pshufb xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+624]
	pshufb xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+640]
	pshufb xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+656]
	pshufb xmm3, xmm4
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
	movdqu XMMWORD PTR [edi+16], xmm0
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqa xmm5, xmm4
	movdqa xmm0, xmm1
212:
	movdqu XMMWORD PTR [edi+48], xmm5
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm1, XMMWORD PTR [esi]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+16]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+16]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+32]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+16], xmm5
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm1, XMMWORD PTR [esi+32]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [esi+48]
	pxor xmm0, xmm1
	pxor xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+80], xmm0
	paddd xmm0, xmm5
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	movdqa xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+80]
	paddd xmm0, xmm1
	movdqa xmm2, xmm7
	pand xmm2, xmm0
	psrld xmm0, 4
	pand xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [ebx+16]
	pshufb xmm1, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm0
	pxor xmm1, xmm4
	aesenclast xmm1, xmm7
	movdqa xmm2, xmm7
	pand xmm2, xmm1
	psrld xmm1, 4
	pand xmm1, xmm7
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pshufb xmm0, xmm2
	movdqu xmm4, XMMWORD PTR [ebx+80]
	pshufb xmm4, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	pxor xmm0, xmm6
	pxor xmm4, xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pand xmm4, xmm3
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [ebx+144]
	pand xmm1, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm1, xmm3
	movdqu xmm2, XMMWORD PTR [ebx+160]
	pand xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+224]
	pshufb xmm2, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+176]
	pand xmm6, xmm0
	movdqu xmm3, XMMWORD PTR [ebx+240]
	pshufb xmm6, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+128]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [ebx+192]
	pshufb xmm0, xmm3
	pxor xmm0, xmm1
	pxor xmm2, xmm6
	pxor xmm0, xmm2
	paddd xmm5, xmm0
	movdqu xmm1, XMMWORD PTR [edi+48]
	pxor xmm5, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	add esi, 64
	sub eax, 1
	jne 212b
	movdqa xmm1, xmm0
	movdqa xmm0, xmm5
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm3, XMMWORD PTR [edi+32]
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
	movdqu xmm2, XMMWORD PTR [ebx+256]
	pshufb xmm0, xmm2
	pshufb xmm3, xmm2
	pshufb xmm4, xmm2
	pshufb xmm1, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu XMMWORD PTR [edi+640], xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	mov esi, DWORD PTR [edi+688]
	mov ebp, DWORD PTR [edi+692]
	mov eax, DWORD PTR [edi+608]
	xor eax, DWORD PTR [edi+696]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+612]
	xor eax, DWORD PTR [edi+700]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+616]
	xor eax, DWORD PTR [edi+704]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+620]
	xor eax, DWORD PTR [edi+708]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+696], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+700], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+704], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+708], eax
	mov eax, DWORD PTR [edi+608]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+612]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+616]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+620]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+688], esi
	mov DWORD PTR [edi+692], ebp
	jne 211b
	jmp 210f
29:
210:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+696]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+700]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+704]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+708]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+672]
	mov esi, DWORD PTR [edi+676]
	mov ebp, DWORD PTR [edi+684]
	mov edi, DWORD PTR [edi+680]
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
	mov DWORD PTR [esp+728], ecx
	mov DWORD PTR [esp+732], ecx
	lea esp, [esp+740]
	lea esp, [esp-744]
	mov ecx, 0
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+740], ecx
	lea esp, [esp+744]
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

vg_seed_cbc_decrypt_chained:
	lea esp, [esp-1860]
	mov eax, DWORD PTR [esp+1864]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+1868]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+1872]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+1876]
	mov DWORD PTR [esp+16], eax
	mov eax, esp
	add eax, 24
	mov DWORD PTR [esp+20], eax
	mov eax, DWORD PTR [esp+20]
	mov DWORD PTR [eax+1792], ebx
	mov DWORD PTR [eax+1796], esi
	mov DWORD PTR [eax+1800], edi
	mov DWORD PTR [eax+1804], ebp
	mov edi, eax
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_SEED_SSE2}
	pop ecx
	mov DWORD PTR [edi+480], eax
	movdqu xmm0, XMMWORD PTR [eax]
	mov eax, DWORD PTR [esp+4]
	add eax, 120
	mov esi, edi
	add esi, 1280
	mov ecx, 16
20:
	movq xmm0, QWORD PTR [eax]
	pshufd xmm1, xmm0, 0
	movdqu XMMWORD PTR [esi], xmm1
	pshufd xmm1, xmm0, 85
	movdqu XMMWORD PTR [esi+16], xmm1
	sub eax, 8
	add esi, 32
	sub ecx, 1
	jne 20b
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [edi+1812], eax
	test eax, eax
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 16
	jb 21f
23:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+1276], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1044]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1048]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1052]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1060]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1064]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1068]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1088]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1104]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1108]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1112]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1116]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1120]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1124]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1128]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1132]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1136]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1140]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1144]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1148]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [esi+124], eax
	mov eax, DWORD PTR [edi+1152]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1152], eax
	mov eax, DWORD PTR [edi+1156]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1156], eax
	mov eax, DWORD PTR [edi+1160]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1160], eax
	mov eax, DWORD PTR [edi+1164]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1164], eax
	mov eax, DWORD PTR [esi+128]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+132]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+136]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+140]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [esi+128], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [esi+132], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [esi+136], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [esi+140], eax
	mov eax, DWORD PTR [edi+1168]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1168], eax
	mov eax, DWORD PTR [edi+1172]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1172], eax
	mov eax, DWORD PTR [edi+1176]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1176], eax
	mov eax, DWORD PTR [edi+1180]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1180], eax
	mov eax, DWORD PTR [esi+144]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+148]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+152]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+156]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [esi+144], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [esi+148], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [esi+152], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [esi+156], eax
	mov eax, DWORD PTR [edi+1184]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1184], eax
	mov eax, DWORD PTR [edi+1188]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1188], eax
	mov eax, DWORD PTR [edi+1192]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1192], eax
	mov eax, DWORD PTR [edi+1196]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1196], eax
	mov eax, DWORD PTR [esi+160]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+164]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+168]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+172]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [esi+160], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [esi+164], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [esi+168], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [esi+172], eax
	mov eax, DWORD PTR [edi+1200]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1200], eax
	mov eax, DWORD PTR [edi+1204]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1204], eax
	mov eax, DWORD PTR [edi+1208]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1208], eax
	mov eax, DWORD PTR [edi+1212]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1212], eax
	mov eax, DWORD PTR [esi+176]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+180]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+184]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+188]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [esi+176], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [esi+180], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [esi+184], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [esi+188], eax
	mov eax, DWORD PTR [edi+1216]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1216], eax
	mov eax, DWORD PTR [edi+1220]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1220], eax
	mov eax, DWORD PTR [edi+1224]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1224], eax
	mov eax, DWORD PTR [edi+1228]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1228], eax
	mov eax, DWORD PTR [esi+192]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+196]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+200]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+204]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [esi+192], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [esi+196], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [esi+200], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [esi+204], eax
	mov eax, DWORD PTR [edi+1232]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1232], eax
	mov eax, DWORD PTR [edi+1236]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1236], eax
	mov eax, DWORD PTR [edi+1240]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1240], eax
	mov eax, DWORD PTR [edi+1244]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1244], eax
	mov eax, DWORD PTR [esi+208]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+212]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+216]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+220]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [esi+208], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [esi+212], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [esi+216], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [esi+220], eax
	mov eax, DWORD PTR [edi+1248]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1248], eax
	mov eax, DWORD PTR [edi+1252]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1252], eax
	mov eax, DWORD PTR [edi+1256]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1256], eax
	mov eax, DWORD PTR [edi+1260]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1260], eax
	mov eax, DWORD PTR [esi+224]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+228]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+232]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+236]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [esi+224], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [esi+228], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [esi+232], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [esi+236], eax
	mov eax, DWORD PTR [edi+1264]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1264], eax
	mov eax, DWORD PTR [edi+1268]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1268], eax
	mov eax, DWORD PTR [edi+1272]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1272], eax
	mov eax, DWORD PTR [edi+1276]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1276], eax
	mov eax, DWORD PTR [esi+240]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+244]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+248]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+252]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [esi+240], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [esi+244], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [esi+248], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [esi+252], eax
	add esi, 256
	sub ebp, 16
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 16
	jae 23b
	jmp 22f
21:
22:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 8
	jb 24f
26:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1148], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1044]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1048]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1052]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1060]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1064]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1068]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	mov eax, DWORD PTR [edi+1088]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1092]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1096]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1100]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [esi+64]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+68]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+72]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+76]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [esi+64], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [esi+68], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [esi+72], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [esi+76], eax
	mov eax, DWORD PTR [edi+1104]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1108]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1112]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1116]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [esi+80]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+84]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+88]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+92]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [esi+80], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [esi+84], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [esi+88], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [esi+92], eax
	mov eax, DWORD PTR [edi+1120]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1124]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1128]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1132]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [esi+96]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+100]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+104]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+108]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [esi+96], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [esi+100], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [esi+104], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [esi+108], eax
	mov eax, DWORD PTR [edi+1136]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1140]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1144]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1148]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [esi+112]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+116]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+120]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+124]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [esi+112], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [esi+116], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [esi+120], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [esi+124], eax
	add esi, 128
	sub ebp, 8
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 8
	jae 26b
	jmp 25f
24:
25:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 4
	jb 27f
29:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1084], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1044]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1048]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1052]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	mov eax, DWORD PTR [edi+1056]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1060]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1064]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1068]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [esi+32]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+36]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+40]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+44]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [esi+32], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [esi+36], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [esi+40], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [esi+44], eax
	mov eax, DWORD PTR [edi+1072]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1076]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1080]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1084]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [esi+48]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+52]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+56]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+60]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [esi+48], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [esi+52], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [esi+56], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [esi+60], eax
	add esi, 64
	sub ebp, 4
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 4
	jae 29b
	jmp 28f
27:
28:
	mov eax, DWORD PTR [edi+1812]
	cmp eax, 2
	jb 210f
212:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1052], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	mov eax, DWORD PTR [edi+1040]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1044]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1048]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1052]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [esi+16]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+20]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+24]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+28]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [esi+16], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [esi+20], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [esi+24], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [esi+28], eax
	add esi, 32
	sub ebp, 2
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	cmp ebp, 2
	jae 212b
	jmp 211f
210:
211:
	mov eax, DWORD PTR [edi+1812]
	test eax, eax
	je 213f
215:
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1036], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	mov eax, DWORD PTR [edi+1024]
	xor eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1028]
	xor eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1032]
	xor eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1036]
	xor eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [esi]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [esi+4]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [esi+8]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [esi+12]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 1
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	jne 215b
	jmp 214f
213:
214:
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [edi+1824]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [edi+1828]
	mov DWORD PTR [esi+12], eax
	mov ebx, DWORD PTR [edi+1792]
	mov esi, DWORD PTR [edi+1796]
	mov ebp, DWORD PTR [edi+1804]
	mov edi, DWORD PTR [edi+1800]
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
	movdqu XMMWORD PTR [esp+1560], xmm0
	movdqu XMMWORD PTR [esp+1576], xmm0
	movdqu XMMWORD PTR [esp+1592], xmm0
	movdqu XMMWORD PTR [esp+1608], xmm0
	movdqu XMMWORD PTR [esp+1624], xmm0
	movdqu XMMWORD PTR [esp+1640], xmm0
	movdqu XMMWORD PTR [esp+1656], xmm0
	movdqu XMMWORD PTR [esp+1672], xmm0
	movdqu XMMWORD PTR [esp+1688], xmm0
	movdqu XMMWORD PTR [esp+1704], xmm0
	movdqu XMMWORD PTR [esp+1720], xmm0
	movdqu XMMWORD PTR [esp+1736], xmm0
	movdqu XMMWORD PTR [esp+1752], xmm0
	movdqu XMMWORD PTR [esp+1768], xmm0
	movdqu XMMWORD PTR [esp+1784], xmm0
	movdqu XMMWORD PTR [esp+1800], xmm0
	movdqu XMMWORD PTR [esp+1816], xmm0
	movdqu XMMWORD PTR [esp+1832], xmm0
	mov DWORD PTR [esp+1848], ecx
	mov DWORD PTR [esp+1852], ecx
	lea esp, [esp+1860]
	lea esp, [esp-1868]
	mov ecx, 0
	mov DWORD PTR [esp], ecx
	mov DWORD PTR [esp+4], ecx
	mov DWORD PTR [esp+8], ecx
	mov DWORD PTR [esp+12], ecx
	mov DWORD PTR [esp+16], ecx
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+1864], ecx
	lea esp, [esp+1868]
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
