// The functions of `src/internal/vg_rc2_encrypt_block.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_encrypt_block:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebp
	mov DWORD PTR [eax+4], ebx
	mov DWORD PTR [eax+8], esi
	mov DWORD PTR [eax+12], edi
	mov DWORD PTR [eax+16], ecx
	mov ebp, eax
	mov edi, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [esi]
	mov ecx, DWORD PTR [esi+4]
	mov ebx, eax
	shr ebx, 16
	mov edx, ecx
	shr edx, 16
	add eax, DWORD PTR [edi]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+2]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+4]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+6]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+8]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+10]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+12]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+14]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+16]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+18]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+20]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+22]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+24]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+26]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+28]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+30]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+32]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+34]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+36]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+38]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	movd xmm7, edx
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add eax, esi
	movd xmm7, eax
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add ebx, esi
	movd xmm7, ebx
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add ecx, esi
	movd xmm7, ecx
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add edx, esi
	add eax, DWORD PTR [edi+40]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+42]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+44]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+46]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+48]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+50]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+52]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+54]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+56]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+58]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+60]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+62]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+64]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+66]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+68]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+70]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+72]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+74]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+78]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+80]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+82]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+84]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+86]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	movd xmm7, edx
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add eax, esi
	movd xmm7, eax
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add ebx, esi
	movd xmm7, ebx
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add ecx, esi
	movd xmm7, ecx
	pshuflw xmm7, xmm7, 0
	punpcklqdq xmm7, xmm7
	movdqa xmm6, xmm7
	pslld xmm6, 10
	psraw xmm6, 15
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm4, XMMWORD PTR [edi+64]
	pxor xmm4, xmm0
	pand xmm4, xmm6
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm1
	pand xmm5, xmm6
	pxor xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm5, XMMWORD PTR [edi+112]
	pxor xmm5, xmm3
	pand xmm5, xmm6
	pxor xmm3, xmm5
	movdqa xmm6, xmm7
	pslld xmm6, 11
	psraw xmm6, 15
	pxor xmm2, xmm0
	pand xmm2, xmm6
	pxor xmm0, xmm2
	pxor xmm3, xmm1
	pand xmm3, xmm6
	pxor xmm1, xmm3
	movdqa xmm6, xmm7
	pslld xmm6, 12
	psraw xmm6, 15
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 13
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 8
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 14
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 4
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movdqa xmm6, xmm7
	pslld xmm6, 15
	psraw xmm6, 15
	movdqa xmm1, xmm0
	psrldq xmm1, 2
	pxor xmm1, xmm0
	pand xmm1, xmm6
	pxor xmm0, xmm1
	movq QWORD PTR [ebp+48], xmm0
	mov esi, DWORD PTR [ebp+48]
	add edx, esi
	add eax, DWORD PTR [edi+88]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+90]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+92]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+94]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+96]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+98]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+100]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+102]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+104]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+106]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+108]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+110]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+112]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+114]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+116]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	add edx, DWORD PTR [edi+118]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	add eax, DWORD PTR [edi+120]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	add ebx, DWORD PTR [edi+122]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	add ecx, DWORD PTR [edi+124]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	mov esi, DWORD PTR [edi+124]
	shr esi, 16
	add edx, esi
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	mov esi, DWORD PTR [esp+8]
	and eax, 65535
	ror ebx, 16
	and ebx, -65536
	or eax, ebx
	and ecx, 65535
	ror edx, 16
	and edx, -65536
	or ecx, edx
	mov DWORD PTR [esi], eax
	mov DWORD PTR [esi+4], ecx
	mov eax, ebp
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	mov ecx, DWORD PTR [eax+16]
	ret
	.p2align 6
