// The functions of `src/internal/vg_seed_crypt16_sse2.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_crypt16_sse2:
	movdqu xmm6, XMMWORD PTR [ebx+48]
	movdqu xmm0, XMMWORD PTR [edi+1024]
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+1040]
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu xmm2, XMMWORD PTR [edi+1056]
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [edi+1072]
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	movdqu XMMWORD PTR [edi+768], xmm0
	movdqu XMMWORD PTR [edi+832], xmm1
	movdqu XMMWORD PTR [edi+896], xmm2
	movdqu XMMWORD PTR [edi+960], xmm3
	movdqu xmm0, XMMWORD PTR [edi+1088]
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+1104]
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu xmm2, XMMWORD PTR [edi+1120]
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [edi+1136]
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	movdqu XMMWORD PTR [edi+784], xmm0
	movdqu XMMWORD PTR [edi+848], xmm1
	movdqu XMMWORD PTR [edi+912], xmm2
	movdqu XMMWORD PTR [edi+976], xmm3
	movdqu xmm0, XMMWORD PTR [edi+1152]
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+1168]
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu xmm2, XMMWORD PTR [edi+1184]
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [edi+1200]
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	movdqu XMMWORD PTR [edi+800], xmm0
	movdqu XMMWORD PTR [edi+864], xmm1
	movdqu XMMWORD PTR [edi+928], xmm2
	movdqu XMMWORD PTR [edi+992], xmm3
	movdqu xmm0, XMMWORD PTR [edi+1216]
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+1232]
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu xmm2, XMMWORD PTR [edi+1248]
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu xmm3, XMMWORD PTR [edi+1264]
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	movdqu XMMWORD PTR [edi+816], xmm0
	movdqu XMMWORD PTR [edi+880], xmm1
	movdqu XMMWORD PTR [edi+944], xmm2
	movdqu XMMWORD PTR [edi+1008], xmm3
20:
	movdqu xmm6, XMMWORD PTR [esi]
	movdqu xmm7, XMMWORD PTR [esi+16]
	movdqu xmm0, XMMWORD PTR [edi+896]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm1, XMMWORD PTR [edi+960]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+912]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm1, XMMWORD PTR [edi+976]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+928]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm1, XMMWORD PTR [edi+992]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+944]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm1, XMMWORD PTR [edi+1008]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm1, XMMWORD PTR [edi+576]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm1, XMMWORD PTR [edi+592]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm1, XMMWORD PTR [edi+608]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu xmm1, XMMWORD PTR [edi+624]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm1, XMMWORD PTR [edi+640]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu XMMWORD PTR [edi+720], xmm0
	movdqu xmm1, XMMWORD PTR [edi+656]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edi+736], xmm0
	movdqu xmm1, XMMWORD PTR [edi+672]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edi+752], xmm0
	movdqu xmm1, XMMWORD PTR [edi+688]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+832]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+832], xmm1
	movdqu xmm1, XMMWORD PTR [edi+704]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+768]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+768], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu xmm1, XMMWORD PTR [edi+848]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+848], xmm1
	movdqu xmm1, XMMWORD PTR [edi+720]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+784]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+784], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm1, XMMWORD PTR [edi+864]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+864], xmm1
	movdqu xmm1, XMMWORD PTR [edi+736]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+800]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+800], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu xmm1, XMMWORD PTR [edi+880]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+880], xmm1
	movdqu xmm1, XMMWORD PTR [edi+752]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+816]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+816], xmm0
	movdqu xmm6, XMMWORD PTR [esi+32]
	movdqu xmm7, XMMWORD PTR [esi+48]
	movdqu xmm0, XMMWORD PTR [edi+768]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm1, XMMWORD PTR [edi+832]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+784]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm1, XMMWORD PTR [edi+848]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+800]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm1, XMMWORD PTR [edi+864]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+816]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm1, XMMWORD PTR [edi+880]
	pxor xmm0, xmm1
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm1, XMMWORD PTR [edi+576]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm1, XMMWORD PTR [edi+592]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm1, XMMWORD PTR [edi+608]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu xmm1, XMMWORD PTR [edi+624]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu xmm1, XMMWORD PTR [edi+640]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu XMMWORD PTR [edi+720], xmm0
	movdqu xmm1, XMMWORD PTR [edi+656]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu XMMWORD PTR [edi+736], xmm0
	movdqu xmm1, XMMWORD PTR [edi+672]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu XMMWORD PTR [edi+752], xmm0
	movdqu xmm1, XMMWORD PTR [edi+688]
	paddd xmm0, xmm1
	movdqu XMMWORD PTR [edi+560], xmm0
	call {vg_seed_g16_sse2}
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+960]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+960], xmm1
	movdqu xmm1, XMMWORD PTR [edi+704]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+896]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+896], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu xmm1, XMMWORD PTR [edi+976]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+976], xmm1
	movdqu xmm1, XMMWORD PTR [edi+720]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+912]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+912], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm1, XMMWORD PTR [edi+992]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+992], xmm1
	movdqu xmm1, XMMWORD PTR [edi+736]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+928]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+928], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqu xmm1, XMMWORD PTR [edi+1008]
	pxor xmm1, xmm0
	movdqu XMMWORD PTR [edi+1008], xmm1
	movdqu xmm1, XMMWORD PTR [edi+752]
	paddd xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+944]
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+944], xmm0
	add esi, 64
	sub ecx, 1
	jne 20b
	movdqu xmm6, XMMWORD PTR [ebx+48]
	movdqu xmm0, XMMWORD PTR [edi+896]
	movdqu xmm1, XMMWORD PTR [edi+960]
	movdqu xmm2, XMMWORD PTR [edi+768]
	movdqu xmm3, XMMWORD PTR [edi+832]
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+1024], xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+1040], xmm1
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+1056], xmm2
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi+1072], xmm3
	movdqu xmm0, XMMWORD PTR [edi+912]
	movdqu xmm1, XMMWORD PTR [edi+976]
	movdqu xmm2, XMMWORD PTR [edi+784]
	movdqu xmm3, XMMWORD PTR [edi+848]
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+1088], xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+1104], xmm1
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+1120], xmm2
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi+1136], xmm3
	movdqu xmm0, XMMWORD PTR [edi+928]
	movdqu xmm1, XMMWORD PTR [edi+992]
	movdqu xmm2, XMMWORD PTR [edi+800]
	movdqu xmm3, XMMWORD PTR [edi+864]
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+1152], xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+1168], xmm1
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+1184], xmm2
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi+1200], xmm3
	movdqu xmm0, XMMWORD PTR [edi+944]
	movdqu xmm1, XMMWORD PTR [edi+1008]
	movdqu xmm2, XMMWORD PTR [edi+816]
	movdqu xmm3, XMMWORD PTR [edi+880]
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm1, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm1, xmm2
	movdqa xmm2, xmm4
	punpcklqdq xmm2, xmm5
	movdqa xmm3, xmm4
	punpckhqdq xmm3, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	movdqa xmm7, xmm0
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm0, xmm6
	pslld xmm0, 8
	pxor xmm0, xmm7
	movdqu XMMWORD PTR [edi+1216], xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	movdqa xmm7, xmm1
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm1, xmm6
	pslld xmm1, 8
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+1232], xmm1
	pshuflw xmm2, xmm2, 177
	pshufhw xmm2, xmm2, 177
	movdqa xmm7, xmm2
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm2, xmm6
	pslld xmm2, 8
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+1248], xmm2
	pshuflw xmm3, xmm3, 177
	pshufhw xmm3, xmm3, 177
	movdqa xmm7, xmm3
	psrld xmm7, 8
	pand xmm7, xmm6
	pand xmm3, xmm6
	pslld xmm3, 8
	pxor xmm3, xmm7
	movdqu XMMWORD PTR [edi+1264], xmm3
	ret
	.p2align 6
