// The functions of `src/internal/vg_sha256_compress_shani.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress_shani:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+96], ebx
	mov DWORD PTR [eax+100], esi
	mov DWORD PTR [eax+104], edi
	mov DWORD PTR [eax+108], ebp
	mov esi, eax
	mov edi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	test ebp, ebp
	mov ebx, DWORD PTR [esp+4]
	mov eax, 66051
	movd xmm0, eax
	mov eax, 67438087
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 134810123
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 202182159
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	movdqu XMMWORD PTR [esi+16], xmm0
	movdqu xmm1, XMMWORD PTR [ebx]
	movdqu xmm2, XMMWORD PTR [ebx+16]
	pshufd xmm1, xmm1, 177
	pshufd xmm2, xmm2, 177
	movdqa xmm7, xmm2
	punpcklqdq xmm7, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm1, xmm7
	je 20f
22:
	movdqu XMMWORD PTR [esi+32], xmm1
	movdqu XMMWORD PTR [esi+48], xmm2
	movdqu xmm3, XMMWORD PTR [edi]
	movdqu xmm0, XMMWORD PTR [esi+16]
	pshufb xmm3, xmm0
	mov eax, 1116352408
	movd xmm0, eax
	mov eax, 1899447441
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -1245643825
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -373957723
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm0, XMMWORD PTR [esi+16]
	pshufb xmm4, xmm0
	mov eax, 961987163
	movd xmm0, eax
	mov eax, 1508970993
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -1841331548
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -1424204075
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm0, XMMWORD PTR [esi+16]
	pshufb xmm5, xmm0
	mov eax, -670586216
	movd xmm0, eax
	mov eax, 310598401
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 607225278
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 1426881987
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm6, XMMWORD PTR [edi+48]
	movdqu xmm0, XMMWORD PTR [esi+16]
	pshufb xmm6, xmm0
	mov eax, 1925078388
	movd xmm0, eax
	mov eax, -2132889090
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -1680079193
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -1046744716
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	mov eax, -459576895
	movd xmm0, eax
	mov eax, -272742522
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 264347078
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 604807628
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	mov eax, 770255983
	movd xmm0, eax
	mov eax, 1249150122
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 1555081692
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 1996064986
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	mov eax, -1740746414
	movd xmm0, eax
	mov eax, -1473132947
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -1341970488
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -1084653625
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	mov eax, -958395405
	movd xmm0, eax
	mov eax, -710438585
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 113926993
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 338241895
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	mov eax, 666307205
	movd xmm0, eax
	mov eax, 773529912
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 1294757372
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 1396182291
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	mov eax, 1695183700
	movd xmm0, eax
	mov eax, 1986661051
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -2117940946
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -1838011259
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	mov eax, -1564481375
	movd xmm0, eax
	mov eax, -1474664885
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -1035236496
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -949202525
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	mov eax, -778901479
	movd xmm0, eax
	mov eax, -694614492
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -200395387
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 275423344
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm3, xmm4
	movdqa xmm7, xmm6
	palignr xmm7, xmm5, 4
	paddd xmm3, xmm7
	sha256msg2 xmm3, xmm6
	mov eax, 430227734
	movd xmm0, eax
	mov eax, 506948616
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 659060556
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 883997877
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm3
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm4, xmm5
	movdqa xmm7, xmm3
	palignr xmm7, xmm6, 4
	paddd xmm4, xmm7
	sha256msg2 xmm4, xmm3
	mov eax, 958139571
	movd xmm0, eax
	mov eax, 1322822218
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, 1537002063
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, 1747873779
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm4
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm5, xmm6
	movdqa xmm7, xmm4
	palignr xmm7, xmm3, 4
	paddd xmm5, xmm7
	sha256msg2 xmm5, xmm4
	mov eax, 1955562222
	movd xmm0, eax
	mov eax, 2024104815
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -2067236844
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -1933114872
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm5
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	sha256msg1 xmm6, xmm3
	movdqa xmm7, xmm5
	palignr xmm7, xmm4, 4
	paddd xmm6, xmm7
	sha256msg2 xmm6, xmm5
	mov eax, -1866530822
	movd xmm0, eax
	mov eax, -1538233109
	movd xmm7, eax
	punpckldq xmm0, xmm7
	mov eax, -1090935817
	movd xmm7, eax
	punpcklqdq xmm0, xmm7
	mov eax, -965641998
	movd xmm7, eax
	pslldq xmm7, 12
	por xmm0, xmm7
	paddd xmm0, xmm6
	sha256rnds2 xmm2, xmm1, xmm0
	pshufd xmm0, xmm0, 14
	sha256rnds2 xmm1, xmm2, xmm0
	movdqu xmm7, XMMWORD PTR [esi+32]
	paddd xmm1, xmm7
	movdqu xmm7, XMMWORD PTR [esi+48]
	paddd xmm2, xmm7
	add edi, 64
	sub ebp, 1
	jne 22b
	jmp 21f
20:
21:
	movdqa xmm7, xmm1
	punpckhqdq xmm7, xmm2
	punpcklqdq xmm1, xmm2
	pshufd xmm7, xmm7, 177
	pshufd xmm1, xmm1, 177
	movdqu XMMWORD PTR [ebx], xmm7
	movdqu XMMWORD PTR [ebx+16], xmm1
	mov ebx, DWORD PTR [esi+96]
	mov edi, DWORD PTR [esi+104]
	mov ebp, DWORD PTR [esi+108]
	mov esi, DWORD PTR [esi+100]
	ret
	.p2align 6
