// The functions of `src/internal/vg_camellia_ctr_core_aesni.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr_core_aesni:
	lea esp, [esp-884]
	mov eax, DWORD PTR [esp+888]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+892]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+896]
	mov DWORD PTR [esp+12], eax
	mov eax, DWORD PTR [esp+900]
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+904]
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
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+608], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+612], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+616], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+620], eax
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+624], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+628], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+632], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+636], eax
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
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
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
	mov eax, DWORD PTR [edi+840]
	mov DWORD PTR [edi+592], eax
	mov eax, DWORD PTR [edi+844]
	mov DWORD PTR [edi+596], eax
	mov eax, DWORD PTR [edi+848]
	mov DWORD PTR [edi+600], eax
	mov eax, DWORD PTR [edi+852]
	mov DWORD PTR [edi+604], eax
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
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
	mov eax, DWORD PTR [edi+852]
	bswap eax
	add eax, 1
	bswap eax
	mov DWORD PTR [edi+852], eax
	mov eax, DWORD PTR [edi+848]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+848], eax
	mov eax, DWORD PTR [edi+844]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+844], eax
	mov eax, DWORD PTR [edi+840]
	bswap eax
	adc eax, 0
	bswap eax
	mov DWORD PTR [edi+840], eax
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
	lea esp, [esp+884]
	ret
	.p2align 6
