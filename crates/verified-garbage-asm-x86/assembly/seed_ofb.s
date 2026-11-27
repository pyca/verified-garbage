// The functions of `src/seed_ofb.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_ofb_aesni:
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
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+644]
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+28]
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

vg_seed_ofb:
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
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1828]
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
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+1036]
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

vg_seed_ofb_final_aesni:
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
	mov eax, DWORD PTR [edi+632]
	mov DWORD PTR [edi+16], eax
	mov eax, DWORD PTR [edi+636]
	mov DWORD PTR [edi+20], eax
	mov eax, DWORD PTR [edi+640]
	mov DWORD PTR [edi+24], eax
	mov eax, DWORD PTR [edi+644]
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
	cmp ebp, 16
	jb 25f
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+644], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+16]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+20]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+24]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+28]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+624], esi
	mov DWORD PTR [edi+628], ebp
	jmp 26f
25:
	mov eax, DWORD PTR [edi+16]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+20]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+24]
	mov DWORD PTR [edi+640], eax
	mov eax, DWORD PTR [edi+28]
	mov DWORD PTR [edi+644], eax
	mov ebx, edi
	add ebx, 16
27:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 27b
	mov DWORD PTR [edi+624], esi
	mov DWORD PTR [edi+628], ebp
26:
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

vg_seed_ofb_final:
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
	mov eax, DWORD PTR [edi+1816]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1820]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1824]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1828]
	mov DWORD PTR [edi+1036], eax
	mov ebx, DWORD PTR [edi+480]
	mov ecx, 8
	mov esi, edi
	add esi, 1280
	call {vg_seed_crypt16_sse2}
	mov esi, DWORD PTR [edi+1808]
	mov ebp, DWORD PTR [edi+1812]
	cmp ebp, 16
	jb 24f
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [esi]
	xor eax, DWORD PTR [edi+1024]
	mov DWORD PTR [esi], eax
	mov eax, DWORD PTR [esi+4]
	xor eax, DWORD PTR [edi+1028]
	mov DWORD PTR [esi+4], eax
	mov eax, DWORD PTR [esi+8]
	xor eax, DWORD PTR [edi+1032]
	mov DWORD PTR [esi+8], eax
	mov eax, DWORD PTR [esi+12]
	xor eax, DWORD PTR [edi+1036]
	mov DWORD PTR [esi+12], eax
	add esi, 16
	sub ebp, 16
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
	jmp 25f
24:
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+1828], eax
	mov ebx, edi
	add ebx, 1024
26:
	movzx eax, BYTE PTR [ebx]
	movzx ecx, BYTE PTR [esi]
	xor ecx, eax
	mov BYTE PTR [esi], cl
	add ebx, 1
	add esi, 1
	sub ebp, 1
	jne 26b
	mov DWORD PTR [edi+1808], esi
	mov DWORD PTR [edi+1812], ebp
25:
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
