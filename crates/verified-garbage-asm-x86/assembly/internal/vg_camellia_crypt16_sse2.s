// The functions of `src/internal/vg_camellia_crypt16_sse2.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_crypt16_sse2:
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu xmm1, XMMWORD PTR [edi+832]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+448], xmm2
	movdqu XMMWORD PTR [edi+576], xmm3
	movdqu xmm0, XMMWORD PTR [edi+720]
	movdqu xmm1, XMMWORD PTR [edi+848]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu XMMWORD PTR [edi+592], xmm3
	movdqu xmm0, XMMWORD PTR [edi+736]
	movdqu xmm1, XMMWORD PTR [edi+864]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+480], xmm2
	movdqu XMMWORD PTR [edi+608], xmm3
	movdqu xmm0, XMMWORD PTR [edi+752]
	movdqu xmm1, XMMWORD PTR [edi+880]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+496], xmm2
	movdqu XMMWORD PTR [edi+624], xmm3
	movdqu xmm0, XMMWORD PTR [edi+768]
	movdqu xmm1, XMMWORD PTR [edi+896]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+512], xmm2
	movdqu XMMWORD PTR [edi+640], xmm3
	movdqu xmm0, XMMWORD PTR [edi+784]
	movdqu xmm1, XMMWORD PTR [edi+912]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu XMMWORD PTR [edi+656], xmm3
	movdqu xmm0, XMMWORD PTR [edi+800]
	movdqu xmm1, XMMWORD PTR [edi+928]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqu XMMWORD PTR [edi+672], xmm3
	movdqu xmm0, XMMWORD PTR [edi+816]
	movdqu xmm1, XMMWORD PTR [edi+944]
	movdqa xmm2, xmm0
	pand xmm2, xmm7
	movdqa xmm3, xmm1
	pand xmm3, xmm7
	pslld xmm3, 8
	pxor xmm2, xmm3
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm1
	pxor xmm0, xmm4
	movdqa xmm3, xmm2
	punpcklwd xmm2, xmm0
	punpckhwd xmm3, xmm0
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqu XMMWORD PTR [edi+688], xmm3
	movdqu xmm7, XMMWORD PTR [ebx+16]
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+464]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+464], xmm1
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu XMMWORD PTR [edi+496], xmm1
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+32]
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+480]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+480], xmm1
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+464], xmm0
	movdqu XMMWORD PTR [edi+496], xmm1
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+48]
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+512]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+464], xmm0
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqu xmm1, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm0, XMMWORD PTR [edi+496]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+496], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+16]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+592]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+592], xmm1
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm1
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu XMMWORD PTR [edi+656], xmm1
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu XMMWORD PTR [edi+688], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+32]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+608], xmm1
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu XMMWORD PTR [edi+624], xmm1
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu xmm1, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu XMMWORD PTR [edi+672], xmm1
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu XMMWORD PTR [edi+688], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+48]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+640]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+640], xmm1
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu XMMWORD PTR [edi+656], xmm1
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqu xmm1, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+672], xmm1
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+688], xmm1
	movdqu xmm6, XMMWORD PTR [esi]
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+464], xmm0
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu xmm0, XMMWORD PTR [edi+496]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+496], xmm0
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+560], xmm0
	movdqu xmm6, XMMWORD PTR [esi+16]
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+688], xmm0
20:
	mov edx, 3
21:
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
	add esi, 32
	sub edx, 1
	jne 21b
	sub ecx, 1
	je 22f
	movdqu xmm6, XMMWORD PTR [esi+32]
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	pand xmm0, xmm1
	pshuflw xmm0, xmm0, 57
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+448]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+448], xmm2
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+464]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+480]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+480], xmm2
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+496]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+496], xmm2
	movdqu xmm0, XMMWORD PTR [edi+496]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+512]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+512], xmm2
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+528]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+544]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+560]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+448]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+448], xmm2
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+464]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+480]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+480], xmm2
	movdqu xmm0, XMMWORD PTR [edi+496]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+496]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+496], xmm2
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+512]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+512], xmm2
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+528]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+544]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+560]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+560], xmm2
	movdqu xmm6, XMMWORD PTR [esi+48]
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+576]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+592]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+592], xmm2
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+608]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+608], xmm2
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+624]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+624], xmm2
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+640]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+640], xmm2
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+656]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+656], xmm2
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+672]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+672], xmm2
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	por xmm1, xmm0
	psrldq xmm1, 8
	movdqu xmm2, XMMWORD PTR [edi+688]
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+688], xmm2
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	pand xmm0, xmm1
	pshuflw xmm0, xmm0, 57
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+576]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+592]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+592], xmm2
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+608]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+608], xmm2
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+624]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+624], xmm2
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+640]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+640], xmm2
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+656]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+656], xmm2
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+672]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+672], xmm2
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	pand xmm0, xmm1
	pslldq xmm0, 8
	movdqu xmm2, XMMWORD PTR [edi+688]
	pxor xmm2, xmm0
	movdqu XMMWORD PTR [edi+688], xmm2
	add esi, 32
	test ecx, ecx
	jmp 23f
22:
23:
	jne 20b
	movdqu xmm6, XMMWORD PTR [esi+32]
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+688], xmm0
	movdqu xmm6, XMMWORD PTR [esi+48]
	movdqu xmm5, XMMWORD PTR [ebx+128]
	pxor xmm6, xmm5
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqa xmm1, xmm6
	pslld xmm1, 15
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqa xmm1, xmm6
	pslld xmm1, 14
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+464], xmm0
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqa xmm1, xmm6
	pslld xmm1, 13
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu xmm0, XMMWORD PTR [edi+496]
	movdqa xmm1, xmm6
	pslld xmm1, 12
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+496], xmm0
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqa xmm1, xmm6
	pslld xmm1, 11
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqa xmm1, xmm6
	pslld xmm1, 10
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqa xmm1, xmm6
	pslld xmm1, 9
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm0, XMMWORD PTR [edi+560]
	movdqa xmm1, xmm6
	pslld xmm1, 8
	psraw xmm1, 15
	pxor xmm0, xmm1
	movdqu XMMWORD PTR [edi+560], xmm0
	movdqu xmm7, XMMWORD PTR [ebx+16]
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+464]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+464], xmm1
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu XMMWORD PTR [edi+496], xmm1
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu xmm0, XMMWORD PTR [edi+544]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+32]
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+480]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+480], xmm1
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+464], xmm0
	movdqu XMMWORD PTR [edi+496], xmm1
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm0, XMMWORD PTR [edi+528]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+48]
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+512]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+512], xmm1
	movdqu xmm0, XMMWORD PTR [edi+464]
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+464], xmm0
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqu xmm1, XMMWORD PTR [edi+544]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu XMMWORD PTR [edi+544], xmm1
	movdqu xmm0, XMMWORD PTR [edi+496]
	movdqu xmm1, XMMWORD PTR [edi+560]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+496], xmm0
	movdqu XMMWORD PTR [edi+560], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+16]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+592]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+592], xmm1
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+624], xmm1
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu XMMWORD PTR [edi+656], xmm1
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm0
	psrlq xmm2, 1
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 1
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+672], xmm0
	movdqu XMMWORD PTR [edi+688], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+32]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+608]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+608], xmm1
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+624]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu XMMWORD PTR [edi+624], xmm1
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu xmm1, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+640], xmm0
	movdqu XMMWORD PTR [edi+672], xmm1
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm0
	psrlq xmm2, 2
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 2
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+656], xmm0
	movdqu XMMWORD PTR [edi+688], xmm1
	movdqu xmm7, XMMWORD PTR [ebx+48]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+640]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu XMMWORD PTR [edi+640], xmm1
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+656]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu XMMWORD PTR [edi+656], xmm1
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqu xmm1, XMMWORD PTR [edi+672]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu XMMWORD PTR [edi+672], xmm1
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqu xmm1, XMMWORD PTR [edi+688]
	movdqa xmm2, xmm0
	psrlq xmm2, 4
	pxor xmm2, xmm1
	pand xmm2, xmm7
	pxor xmm1, xmm2
	psllq xmm2, 4
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+624], xmm0
	movdqu XMMWORD PTR [edi+688], xmm1
	movdqu xmm7, XMMWORD PTR [ebx]
	movdqu xmm0, XMMWORD PTR [edi+576]
	movdqu xmm1, XMMWORD PTR [edi+448]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+704], xmm3
	movdqu XMMWORD PTR [edi+832], xmm0
	movdqu xmm0, XMMWORD PTR [edi+592]
	movdqu xmm1, XMMWORD PTR [edi+464]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+720], xmm3
	movdqu XMMWORD PTR [edi+848], xmm0
	movdqu xmm0, XMMWORD PTR [edi+608]
	movdqu xmm1, XMMWORD PTR [edi+480]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+736], xmm3
	movdqu XMMWORD PTR [edi+864], xmm0
	movdqu xmm0, XMMWORD PTR [edi+624]
	movdqu xmm1, XMMWORD PTR [edi+496]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+752], xmm3
	movdqu XMMWORD PTR [edi+880], xmm0
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu xmm1, XMMWORD PTR [edi+512]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+768], xmm3
	movdqu XMMWORD PTR [edi+896], xmm0
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqu xmm1, XMMWORD PTR [edi+528]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+784], xmm3
	movdqu XMMWORD PTR [edi+912], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqu xmm1, XMMWORD PTR [edi+544]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+800], xmm3
	movdqu XMMWORD PTR [edi+928], xmm0
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqu xmm1, XMMWORD PTR [edi+560]
	pshuflw xmm0, xmm0, 216
	pshufhw xmm0, xmm0, 216
	pshufd xmm0, xmm0, 216
	pshuflw xmm1, xmm1, 216
	pshufhw xmm1, xmm1, 216
	pshufd xmm1, xmm1, 216
	movdqa xmm2, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm2, xmm1
	movdqa xmm3, xmm0
	pand xmm3, xmm7
	movdqa xmm4, xmm2
	pand xmm4, xmm7
	pslld xmm4, 8
	pxor xmm3, xmm4
	psrld xmm0, 8
	pand xmm0, xmm7
	movdqa xmm4, xmm7
	pandn xmm4, xmm2
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+816], xmm3
	movdqu XMMWORD PTR [edi+944], xmm0
	ret
	.p2align 6
