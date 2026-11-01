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
	mov edi, DWORD PTR [esp+8]
	movzx eax, BYTE PTR [edi]
	movzx edx, BYTE PTR [edi+1]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+64], eax
	movzx eax, BYTE PTR [edi+2]
	movzx edx, BYTE PTR [edi+3]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+68], eax
	movzx eax, BYTE PTR [edi+4]
	movzx edx, BYTE PTR [edi+5]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+72], eax
	movzx eax, BYTE PTR [edi+6]
	movzx edx, BYTE PTR [edi+7]
	ror edx, 24
	or eax, edx
	mov DWORD PTR [ebp+76], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi]
	movzx edi, BYTE PTR [edi+1]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+2]
	movzx edi, BYTE PTR [edi+3]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+4]
	movzx edi, BYTE PTR [edi+5]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+6]
	movzx edi, BYTE PTR [edi+7]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+8]
	movzx edi, BYTE PTR [edi+9]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+10]
	movzx edi, BYTE PTR [edi+11]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+12]
	movzx edi, BYTE PTR [edi+13]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+14]
	movzx edi, BYTE PTR [edi+15]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+16]
	movzx edi, BYTE PTR [edi+17]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+18]
	movzx edi, BYTE PTR [edi+19]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+20]
	movzx edi, BYTE PTR [edi+21]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+22]
	movzx edi, BYTE PTR [edi+23]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+24]
	movzx edi, BYTE PTR [edi+25]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+26]
	movzx edi, BYTE PTR [edi+27]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+28]
	movzx edi, BYTE PTR [edi+29]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+30]
	movzx edi, BYTE PTR [edi+31]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+32]
	movzx edi, BYTE PTR [edi+33]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+34]
	movzx edi, BYTE PTR [edi+35]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+36]
	movzx edi, BYTE PTR [edi+37]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+38]
	movzx edi, BYTE PTR [edi+39]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+76]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+64]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+68]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+72]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	mov eax, DWORD PTR [ebp+72]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+76]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+40]
	movzx edi, BYTE PTR [edi+41]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+42]
	movzx edi, BYTE PTR [edi+43]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+44]
	movzx edi, BYTE PTR [edi+45]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+46]
	movzx edi, BYTE PTR [edi+47]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+48]
	movzx edi, BYTE PTR [edi+49]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+50]
	movzx edi, BYTE PTR [edi+51]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+52]
	movzx edi, BYTE PTR [edi+53]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+54]
	movzx edi, BYTE PTR [edi+55]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+56]
	movzx edi, BYTE PTR [edi+57]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+58]
	movzx edi, BYTE PTR [edi+59]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+60]
	movzx edi, BYTE PTR [edi+61]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+62]
	movzx edi, BYTE PTR [edi+63]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+64]
	movzx edi, BYTE PTR [edi+65]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+66]
	movzx edi, BYTE PTR [edi+67]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+68]
	movzx edi, BYTE PTR [edi+69]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+70]
	movzx edi, BYTE PTR [edi+71]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+72]
	movzx edi, BYTE PTR [edi+73]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+74]
	movzx edi, BYTE PTR [edi+75]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+76]
	movzx edi, BYTE PTR [edi+77]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+78]
	movzx edi, BYTE PTR [edi+79]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+80]
	movzx edi, BYTE PTR [edi+81]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+82]
	movzx edi, BYTE PTR [edi+83]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+84]
	movzx edi, BYTE PTR [edi+85]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+86]
	movzx edi, BYTE PTR [edi+87]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+76]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+64]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+64], edx
	mov eax, DWORD PTR [ebp+64]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+68]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+68], edx
	mov eax, DWORD PTR [ebp+68]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+72]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+72], edx
	mov eax, DWORD PTR [ebp+72]
	mov edi, DWORD PTR [esp+4]
	and eax, 63
	mov ebx, eax
	shr eax, 1
	movd xmm0, eax
	pshufd xmm0, xmm0, 0
	mov ecx, 1
	movd xmm2, ecx
	pshufd xmm2, xmm2, 17
	mov ecx, 2
	movd xmm3, ecx
	pshufd xmm3, xmm3, 5
	paddd xmm2, xmm3
	mov ecx, 4
	movd xmm3, ecx
	pshufd xmm3, xmm3, 0
	mov ecx, -1
	movd xmm6, ecx
	pshufd xmm6, xmm6, 0
	pxor xmm1, xmm1
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+16]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+48]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+64]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+80]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+96]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqa xmm4, xmm0
	pxor xmm4, xmm2
	paddd xmm4, xmm6
	psrld xmm4, 8
	movdqa xmm7, xmm4
	pslld xmm7, 8
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+112]
	pand xmm5, xmm4
	por xmm1, xmm5
	paddd xmm2, xmm3
	movdqu XMMWORD PTR [ebp+48], xmm1
	mov eax, DWORD PTR [ebp+48]
	or eax, DWORD PTR [ebp+52]
	or eax, DWORD PTR [ebp+56]
	or eax, DWORD PTR [ebp+60]
	and ebx, 1
	xor ebx, -1
	add ebx, 1
	mov ecx, eax
	shr ecx, 16
	and ecx, ebx
	xor ebx, -1
	and eax, ebx
	and eax, 65535
	or eax, ecx
	mov edx, DWORD PTR [ebp+76]
	add edx, eax
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+88]
	movzx edi, BYTE PTR [edi+89]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+90]
	movzx edi, BYTE PTR [edi+91]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+92]
	movzx edi, BYTE PTR [edi+93]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+94]
	movzx edi, BYTE PTR [edi+95]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+96]
	movzx edi, BYTE PTR [edi+97]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+98]
	movzx edi, BYTE PTR [edi+99]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+100]
	movzx edi, BYTE PTR [edi+101]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+102]
	movzx edi, BYTE PTR [edi+103]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+104]
	movzx edi, BYTE PTR [edi+105]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+106]
	movzx edi, BYTE PTR [edi+107]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+108]
	movzx edi, BYTE PTR [edi+109]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+110]
	movzx edi, BYTE PTR [edi+111]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+112]
	movzx edi, BYTE PTR [edi+113]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+114]
	movzx edi, BYTE PTR [edi+115]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+116]
	movzx edi, BYTE PTR [edi+117]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+118]
	movzx edi, BYTE PTR [edi+119]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ecx
	xor esi, ebx
	and esi, edx
	xor esi, ebx
	add eax, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+120]
	movzx edi, BYTE PTR [edi+121]
	ror edi, 24
	or esi, edi
	add eax, esi
	and eax, 65535
	mov esi, eax
	shr esi, 15
	ror eax, 31
	or eax, esi
	and eax, 65535
	mov DWORD PTR [ebp+64], eax
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, edx
	xor esi, ecx
	and esi, eax
	xor esi, ecx
	add ebx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+122]
	movzx edi, BYTE PTR [edi+123]
	ror edi, 24
	or esi, edi
	add ebx, esi
	and ebx, 65535
	mov esi, ebx
	shr esi, 14
	ror ebx, 30
	or ebx, esi
	and ebx, 65535
	mov DWORD PTR [ebp+68], ebx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, eax
	xor esi, edx
	and esi, ebx
	xor esi, edx
	add ecx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+124]
	movzx edi, BYTE PTR [edi+125]
	ror edi, 24
	or esi, edi
	add ecx, esi
	and ecx, 65535
	mov esi, ecx
	shr esi, 13
	ror ecx, 29
	or ecx, esi
	and ecx, 65535
	mov DWORD PTR [ebp+72], ecx
	mov eax, DWORD PTR [ebp+64]
	mov ebx, DWORD PTR [ebp+68]
	mov ecx, DWORD PTR [ebp+72]
	mov edx, DWORD PTR [ebp+76]
	mov esi, ebx
	xor esi, eax
	and esi, ecx
	xor esi, eax
	add edx, esi
	mov edi, DWORD PTR [esp+4]
	movzx esi, BYTE PTR [edi+126]
	movzx edi, BYTE PTR [edi+127]
	ror edi, 24
	or esi, edi
	add edx, esi
	and edx, 65535
	mov esi, edx
	shr esi, 11
	ror edx, 27
	or edx, esi
	and edx, 65535
	mov DWORD PTR [ebp+76], edx
	mov edi, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebp+64]
	mov BYTE PTR [edi], al
	shr eax, 8
	mov BYTE PTR [edi+1], al
	mov eax, DWORD PTR [ebp+68]
	mov BYTE PTR [edi+2], al
	shr eax, 8
	mov BYTE PTR [edi+3], al
	mov eax, DWORD PTR [ebp+72]
	mov BYTE PTR [edi+4], al
	shr eax, 8
	mov BYTE PTR [edi+5], al
	mov eax, DWORD PTR [ebp+76]
	mov BYTE PTR [edi+6], al
	shr eax, 8
	mov BYTE PTR [edi+7], al
	mov eax, ebp
	mov ebp, DWORD PTR [eax]
	mov ebx, DWORD PTR [eax+4]
	mov esi, DWORD PTR [eax+8]
	mov edi, DWORD PTR [eax+12]
	mov ecx, DWORD PTR [eax+16]
	ret
	.p2align 6
