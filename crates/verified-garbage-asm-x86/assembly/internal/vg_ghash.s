// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	mov ecx, DWORD PTR [esp+20]
	mov DWORD PTR [ecx+208], ebx
	mov DWORD PTR [ecx+212], esi
	mov DWORD PTR [ecx+216], edi
	mov DWORD PTR [ecx+220], ebp
	mov edx, DWORD PTR [esp+12]
	mov DWORD PTR [ecx+224], edx
	mov edx, DWORD PTR [esp+16]
	mov DWORD PTR [ecx+228], edx
	mov edx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edx]
	mov ebx, DWORD PTR [edx+4]
	mov esi, DWORD PTR [edx+8]
	mov edi, DWORD PTR [edx+12]
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	mov ebp, eax
	shr ebp, 31
	add eax, eax
	mov edx, ebx
	shr edx, 31
	xor eax, edx
	add ebx, ebx
	mov edx, esi
	shr edx, 31
	xor ebx, edx
	add esi, esi
	mov edx, edi
	shr edx, 31
	xor esi, edx
	add edi, edi
	xor edi, ebp
	ror ebp, 1
	xor eax, ebp
	ror ebp, 1
	xor eax, ebp
	ror ebp, 5
	xor eax, ebp
	mov DWORD PTR [ecx+140], eax
	mov DWORD PTR [ecx+136], ebx
	mov DWORD PTR [ecx+132], esi
	mov DWORD PTR [ecx+128], edi
	mov eax, DWORD PTR [ecx+128]
	xor eax, DWORD PTR [ecx+132]
	xor eax, DWORD PTR [ecx+136]
	xor eax, DWORD PTR [ecx+140]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+96], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+100], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+104], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+108], edx
	mov eax, 16711935
	movd xmm7, eax
	pshufd xmm7, xmm7, 0
	movdqu xmm0, XMMWORD PTR [ecx+128]
	pshufd xmm1, xmm0, 132
	pshufd xmm2, xmm0, 222
	pxor xmm1, xmm2
	movdqa xmm2, xmm0
	pslld xmm2, 16
	pxor xmm2, xmm0
	psrld xmm2, 16
	movdqa xmm3, xmm1
	pslld xmm3, 16
	pxor xmm3, xmm1
	psrld xmm3, 16
	pslld xmm3, 16
	por xmm2, xmm3
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	pxor xmm0, xmm3
	psrlq xmm0, 8
	movdqu XMMWORD PTR [ecx], xmm3
	movdqu XMMWORD PTR [ecx+16], xmm0
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pxor xmm1, xmm3
	psrlq xmm1, 8
	movdqu XMMWORD PTR [ecx+32], xmm3
	movdqu XMMWORD PTR [ecx+48], xmm1
	movdqa xmm3, xmm2
	pand xmm3, xmm7
	pxor xmm2, xmm3
	psrlq xmm2, 8
	movdqu XMMWORD PTR [ecx+64], xmm3
	movdqu XMMWORD PTR [ecx+80], xmm2
	mov edx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [edx]
	mov ebx, DWORD PTR [edx+4]
	mov esi, DWORD PTR [edx+8]
	mov edi, DWORD PTR [edx+12]
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	mov DWORD PTR [ecx+140], eax
	mov DWORD PTR [ecx+136], ebx
	mov DWORD PTR [ecx+132], esi
	mov DWORD PTR [ecx+128], edi
	mov eax, DWORD PTR [ecx+228]
	test eax, eax
	je 20f
22:
	mov edx, DWORD PTR [ecx+224]
	movdqu xmm0, XMMWORD PTR [edx]
	add edx, 16
	mov DWORD PTR [ecx+224], edx
	movdqa xmm1, xmm0
	pand xmm1, xmm7
	pxor xmm0, xmm1
	psllq xmm1, 8
	psrlq xmm0, 8
	por xmm0, xmm1
	pshuflw xmm0, xmm0, 27
	pshufhw xmm0, xmm0, 27
	pshufd xmm0, xmm0, 78
	movdqu xmm1, XMMWORD PTR [ecx+128]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [ecx+128], xmm0
	mov eax, DWORD PTR [ecx+128]
	xor eax, DWORD PTR [ecx+132]
	xor eax, DWORD PTR [ecx+136]
	xor eax, DWORD PTR [ecx+140]
	mov edx, eax
	and edx, 286331153
	mov DWORD PTR [ecx+112], edx
	mov edx, eax
	and edx, 572662306
	mov DWORD PTR [ecx+116], edx
	mov edx, eax
	and edx, 1145324612
	mov DWORD PTR [ecx+120], edx
	mov edx, eax
	and edx, -2004318072
	mov DWORD PTR [ecx+124], edx
	mov eax, DWORD PTR [ecx+112]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+116]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+120]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+124]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 286331153
	and esi, 286331153
	mov edi, ebx
	mov ebp, esi
	mov eax, DWORD PTR [ecx+112]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+116]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+120]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+124]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 572662306
	and esi, 572662306
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+112]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+116]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+120]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+124]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, 1145324612
	and esi, 1145324612
	xor edi, ebx
	xor ebp, esi
	mov eax, DWORD PTR [ecx+112]
	mov edx, DWORD PTR [ecx+108]
	mul edx
	mov ebx, eax
	mov esi, edx
	mov eax, DWORD PTR [ecx+116]
	mov edx, DWORD PTR [ecx+104]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+120]
	mov edx, DWORD PTR [ecx+100]
	mul edx
	xor ebx, eax
	xor esi, edx
	mov eax, DWORD PTR [ecx+124]
	mov edx, DWORD PTR [ecx+96]
	mul edx
	xor ebx, eax
	xor esi, edx
	and ebx, -2004318072
	and esi, -2004318072
	xor edi, ebx
	xor ebp, esi
	pshufd xmm1, xmm0, 132
	pshufd xmm2, xmm0, 222
	pxor xmm1, xmm2
	movdqa xmm2, xmm0
	pslld xmm2, 16
	pxor xmm2, xmm0
	psrld xmm2, 16
	movdqa xmm3, xmm1
	pslld xmm3, 16
	pxor xmm3, xmm1
	psrld xmm3, 16
	pslld xmm3, 16
	por xmm2, xmm3
	movdqu XMMWORD PTR [ecx+176], xmm1
	movdqu XMMWORD PTR [ecx+192], xmm2
	movdqa xmm1, xmm0
	psllq xmm1, 8
	pxor xmm1, xmm0
	movdqu xmm4, XMMWORD PTR [ecx+16]
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm4
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqu xmm5, XMMWORD PTR [ecx]
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pand xmm3, xmm5
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	pxor xmm4, xmm5
	movdqa xmm5, xmm1
	psraw xmm5, 15
	pand xmm5, xmm4
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	pxor xmm5, xmm2
	pxor xmm5, xmm3
	movdqa xmm4, xmm5
	pand xmm4, xmm7
	pxor xmm5, xmm4
	psllq xmm4, 8
	psrlq xmm5, 8
	pxor xmm3, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm3
	punpcklwd xmm4, xmm2
	punpckhwd xmm3, xmm2
	movdqu XMMWORD PTR [ecx+144], xmm4
	movdqu XMMWORD PTR [ecx+160], xmm3
	movdqu xmm0, XMMWORD PTR [ecx+176]
	movdqa xmm1, xmm0
	psllq xmm1, 8
	pxor xmm1, xmm0
	movdqu xmm4, XMMWORD PTR [ecx+48]
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm4
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqu xmm5, XMMWORD PTR [ecx+32]
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pand xmm3, xmm5
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	pxor xmm4, xmm5
	movdqa xmm5, xmm1
	psraw xmm5, 15
	pand xmm5, xmm4
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	pxor xmm5, xmm2
	pxor xmm5, xmm3
	movdqa xmm4, xmm5
	pand xmm4, xmm7
	pxor xmm5, xmm4
	psllq xmm4, 8
	psrlq xmm5, 8
	pxor xmm3, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm3
	punpcklwd xmm4, xmm2
	punpckhwd xmm3, xmm2
	movdqu XMMWORD PTR [ecx+176], xmm4
	movdqu XMMWORD PTR [ecx+240], xmm3
	movdqu xmm0, XMMWORD PTR [ecx+192]
	movdqa xmm1, xmm0
	psllq xmm1, 8
	pxor xmm1, xmm0
	movdqu xmm4, XMMWORD PTR [ecx+80]
	movdqa xmm2, xmm0
	psraw xmm2, 15
	pand xmm2, xmm4
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm2, xmm2
	pxor xmm2, xmm6
	paddw xmm0, xmm0
	movdqu xmm5, XMMWORD PTR [ecx+64]
	movdqa xmm3, xmm0
	psraw xmm3, 15
	pand xmm3, xmm5
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	paddw xmm0, xmm0
	movdqa xmm6, xmm0
	psraw xmm6, 15
	pand xmm6, xmm5
	paddw xmm3, xmm3
	pxor xmm3, xmm6
	pxor xmm4, xmm5
	movdqa xmm5, xmm1
	psraw xmm5, 15
	pand xmm5, xmm4
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	paddw xmm1, xmm1
	movdqa xmm6, xmm1
	psraw xmm6, 15
	pand xmm6, xmm4
	paddw xmm5, xmm5
	pxor xmm5, xmm6
	pxor xmm5, xmm2
	pxor xmm5, xmm3
	movdqa xmm4, xmm5
	pand xmm4, xmm7
	pxor xmm5, xmm4
	psllq xmm4, 8
	psrlq xmm5, 8
	pxor xmm3, xmm4
	pxor xmm2, xmm5
	movdqa xmm4, xmm3
	punpcklwd xmm4, xmm2
	punpckhwd xmm3, xmm2
	movdqu xmm0, XMMWORD PTR [ecx+144]
	movdqa xmm6, xmm0
	psrlq xmm6, 32
	pxor xmm6, xmm0
	pxor xmm6, xmm4
	psllq xmm6, 32
	psrlq xmm6, 16
	pxor xmm0, xmm6
	movdqu xmm1, XMMWORD PTR [ecx+160]
	movdqa xmm6, xmm1
	psrlq xmm6, 32
	pxor xmm6, xmm1
	pxor xmm6, xmm3
	psllq xmm6, 32
	psrlq xmm6, 16
	pxor xmm1, xmm6
	psrlq xmm4, 32
	psrlq xmm3, 32
	movdqu xmm2, XMMWORD PTR [ecx+176]
	movdqa xmm6, xmm2
	psrlq xmm6, 32
	pxor xmm6, xmm2
	pxor xmm6, xmm4
	psllq xmm6, 32
	psrlq xmm6, 16
	pxor xmm2, xmm6
	movdqu xmm5, XMMWORD PTR [ecx+240]
	movdqa xmm6, xmm5
	psrlq xmm6, 32
	pxor xmm6, xmm5
	pxor xmm6, xmm3
	psllq xmm6, 32
	psrlq xmm6, 16
	pxor xmm5, xmm6
	movd xmm6, edi
	movd xmm3, ebp
	punpckldq xmm6, xmm3
	pshufd xmm3, xmm0, 78
	pxor xmm3, xmm0
	pshufd xmm4, xmm1, 78
	pxor xmm4, xmm1
	punpcklqdq xmm3, xmm4
	pxor xmm5, xmm3
	movdqa xmm3, xmm5
	pxor xmm3, xmm2
	pshufd xmm4, xmm3, 78
	pxor xmm4, xmm3
	pxor xmm4, xmm6
	pslldq xmm4, 8
	psrldq xmm4, 4
	pxor xmm4, xmm2
	pxor xmm4, xmm0
	pxor xmm4, xmm1
	movdqa xmm3, xmm5
	pslldq xmm3, 8
	psrldq xmm3, 4
	pxor xmm0, xmm3
	movdqa xmm3, xmm4
	pslldq xmm3, 8
	pxor xmm0, xmm3
	psrldq xmm5, 8
	pslldq xmm5, 4
	pxor xmm1, xmm5
	psrldq xmm4, 8
	pxor xmm1, xmm4
	movdqa xmm4, xmm0
	psllq xmm4, 57
	movdqa xmm3, xmm4
	psllq xmm4, 5
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm3, xmm4
	pslldq xmm3, 8
	pxor xmm0, xmm3
	movdqa xmm4, xmm0
	psllq xmm4, 57
	movdqa xmm3, xmm4
	psllq xmm4, 5
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm3, xmm4
	psrldq xmm3, 8
	pxor xmm1, xmm3
	pxor xmm1, xmm0
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm1, xmm4
	psrlq xmm4, 1
	pxor xmm1, xmm4
	psrlq xmm4, 5
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [ecx+128], xmm1
	mov eax, DWORD PTR [ecx+228]
	add eax, -1
	mov DWORD PTR [ecx+228], eax
	test eax, eax
	jne 22b
	jmp 21f
20:
21:
	mov eax, DWORD PTR [ecx+140]
	mov ebx, DWORD PTR [ecx+136]
	mov esi, DWORD PTR [ecx+132]
	mov edi, DWORD PTR [ecx+128]
	bswap eax
	bswap ebx
	bswap esi
	bswap edi
	mov DWORD PTR [ecx+128], eax
	mov DWORD PTR [ecx+132], ebx
	mov DWORD PTR [ecx+136], esi
	mov DWORD PTR [ecx+140], edi
	mov ebx, DWORD PTR [ecx+208]
	mov esi, DWORD PTR [ecx+212]
	mov edi, DWORD PTR [ecx+216]
	mov ebp, DWORD PTR [ecx+220]
	mov edx, DWORD PTR [esp+8]
	movdqu xmm0, XMMWORD PTR [ecx+128]
	movdqu XMMWORD PTR [edx], xmm0
	ret
	.p2align 6
