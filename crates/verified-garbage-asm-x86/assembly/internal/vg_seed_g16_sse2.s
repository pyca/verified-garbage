// The functions of `src/internal/vg_seed_g16_sse2.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_g16_sse2:
	movdqu xmm0, XMMWORD PTR [edi+512]
	movdqu xmm1, XMMWORD PTR [edi+528]
	movdqu xmm2, XMMWORD PTR [edi+544]
	movdqu xmm3, XMMWORD PTR [edi+560]
	movdqu xmm6, XMMWORD PTR [ebx]
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm4, xmm1
	pand xmm4, xmm6
	pxor xmm1, xmm4
	psllq xmm4, 1
	pxor xmm0, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm2, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	psllq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 2
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi], xmm0
	psrld xmm0, 4
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu XMMWORD PTR [edi+16], xmm1
	psrld xmm1, 4
	movdqu XMMWORD PTR [edi+80], xmm1
	movdqu XMMWORD PTR [edi+32], xmm2
	psrld xmm2, 4
	movdqu XMMWORD PTR [edi+96], xmm2
	movdqu XMMWORD PTR [edi+48], xmm3
	psrld xmm3, 4
	movdqu XMMWORD PTR [edi+112], xmm3
	movdqu xmm7, XMMWORD PTR [edi+16]
	movdqu xmm6, XMMWORD PTR [edi+32]
	pxor xmm6, xmm7
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+96]
	pxor xmm4, xmm5
	movdqu xmm3, XMMWORD PTR [edi]
	pxor xmm3, xmm4
	movdqu xmm2, XMMWORD PTR [edi+48]
	pxor xmm2, xmm3
	movdqu xmm3, XMMWORD PTR [edi]
	pxor xmm3, xmm7
	movdqu xmm1, XMMWORD PTR [edi]
	movdqu xmm0, XMMWORD PTR [edi+64]
	pxor xmm0, xmm1
	movdqu xmm1, XMMWORD PTR [edi+64]
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqa xmm2, xmm7
	pxor xmm2, xmm1
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu xmm3, XMMWORD PTR [edi+96]
	pxor xmm3, xmm0
	pxor xmm5, xmm0
	movdqa xmm0, xmm2
	pand xmm0, xmm6
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pxor xmm3, xmm5
	movdqu XMMWORD PTR [edi+192], xmm0
	movdqu xmm0, XMMWORD PTR [edi+80]
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm6, XMMWORD PTR [edi+112]
	pxor xmm6, xmm0
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [edi+224], xmm3
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm6
	pxor xmm5, xmm3
	pxor xmm6, xmm7
	pxor xmm4, xmm3
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqa xmm6, xmm4
	pand xmm6, xmm5
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqa xmm5, xmm1
	pand xmm5, xmm3
	movdqu XMMWORD PTR [edi+272], xmm5
	movdqu xmm5, XMMWORD PTR [edi+64]
	pxor xmm5, xmm3
	pxor xmm7, xmm5
	movdqu XMMWORD PTR [edi+288], xmm3
	movdqu xmm3, XMMWORD PTR [edi+160]
	pxor xmm3, xmm5
	movdqa xmm5, xmm7
	pand xmm5, xmm3
	movdqu XMMWORD PTR [edi+304], xmm3
	movdqu xmm3, XMMWORD PTR [edi+160]
	pxor xmm3, xmm1
	movdqu XMMWORD PTR [edi+320], xmm7
	movdqu xmm7, XMMWORD PTR [edi+160]
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edi+336], xmm4
	movdqu xmm4, XMMWORD PTR [edi+112]
	pand xmm4, xmm3
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+48]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+368], xmm1
	movdqu xmm1, XMMWORD PTR [edi+160]
	pand xmm1, xmm3
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm3
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [edi+384], xmm3
	movdqu xmm3, XMMWORD PTR [edi+64]
	pxor xmm3, xmm0
	movdqu XMMWORD PTR [edi+400], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	pand xmm0, xmm3
	pxor xmm5, xmm0
	pxor xmm5, xmm1
	pxor xmm4, xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	pxor xmm0, xmm5
	movdqu xmm5, XMMWORD PTR [edi+80]
	pxor xmm5, xmm2
	movdqu XMMWORD PTR [edi+416], xmm3
	movdqu xmm3, XMMWORD PTR [edi+224]
	pand xmm3, xmm7
	pxor xmm3, xmm6
	pxor xmm4, xmm3
	pxor xmm4, xmm5
	movdqa xmm5, xmm4
	pxor xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+288]
	movdqu XMMWORD PTR [edi+432], xmm7
	movdqu xmm7, XMMWORD PTR [edi+208]
	pxor xmm7, xmm6
	movdqu xmm6, XMMWORD PTR [edi+240]
	pand xmm6, xmm7
	movdqu XMMWORD PTR [edi+448], xmm7
	movdqu xmm7, XMMWORD PTR [edi+192]
	pxor xmm7, xmm6
	pxor xmm7, xmm1
	movdqu xmm1, XMMWORD PTR [edi+272]
	pxor xmm1, xmm6
	pxor xmm1, xmm3
	movdqu xmm3, XMMWORD PTR [edi+400]
	pxor xmm3, xmm7
	movdqu xmm7, XMMWORD PTR [edi+176]
	pxor xmm7, xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm3
	pand xmm7, xmm4
	movdqa xmm6, xmm3
	pxor xmm6, xmm7
	pand xmm6, xmm5
	pxor xmm7, xmm0
	pxor xmm6, xmm0
	pxor xmm4, xmm6
	movdqu xmm5, XMMWORD PTR [edi+208]
	pand xmm5, xmm6
	pand xmm2, xmm6
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm6
	pand xmm0, xmm5
	pxor xmm4, xmm0
	pxor xmm0, xmm7
	movdqu xmm5, XMMWORD PTR [edi+368]
	pand xmm5, xmm4
	pand xmm7, xmm1
	pxor xmm7, xmm3
	pand xmm0, xmm7
	pxor xmm1, xmm0
	movdqu xmm0, XMMWORD PTR [edi+320]
	pand xmm0, xmm7
	pxor xmm0, xmm2
	movdqa xmm3, xmm1
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [edi+320], xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pand xmm0, xmm3
	pxor xmm2, xmm0
	movdqa xmm0, xmm5
	pxor xmm0, xmm2
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm2, XMMWORD PTR [edi+288]
	pand xmm2, xmm4
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [edi+288], xmm5
	movdqu xmm5, XMMWORD PTR [edi+448]
	pand xmm5, xmm4
	movdqu XMMWORD PTR [edi+448], xmm5
	movdqu xmm5, XMMWORD PTR [edi+240]
	pand xmm5, xmm4
	pxor xmm6, xmm7
	movdqu xmm4, XMMWORD PTR [edi+256]
	pand xmm4, xmm6
	movdqu XMMWORD PTR [edi+256], xmm5
	movdqu xmm5, XMMWORD PTR [edi+336]
	pand xmm5, xmm6
	pxor xmm0, xmm5
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [edi+336], xmm0
	movdqu xmm0, XMMWORD PTR [edi+384]
	pand xmm0, xmm3
	movdqu xmm3, XMMWORD PTR [edi+432]
	pand xmm3, xmm6
	pxor xmm5, xmm3
	movdqu XMMWORD PTR [edi+432], xmm5
	movdqu xmm5, XMMWORD PTR [edi+224]
	pand xmm5, xmm6
	movdqa xmm6, xmm4
	pxor xmm6, xmm5
	pxor xmm5, xmm0
	pxor xmm4, xmm0
	pxor xmm3, xmm4
	movdqu xmm0, XMMWORD PTR [edi+352]
	pand xmm0, xmm1
	movdqu XMMWORD PTR [edi+352], xmm3
	movdqu xmm3, XMMWORD PTR [edi+112]
	pand xmm3, xmm1
	pxor xmm1, xmm7
	movdqu XMMWORD PTR [edi+224], xmm0
	movdqu xmm0, XMMWORD PTR [edi+304]
	pand xmm0, xmm7
	movdqu xmm7, XMMWORD PTR [edi+144]
	pand xmm7, xmm1
	movdqu XMMWORD PTR [edi+144], xmm7
	movdqu xmm7, XMMWORD PTR [edi+416]
	pand xmm7, xmm1
	movdqa xmm1, xmm7
	pxor xmm1, xmm3
	pxor xmm3, xmm0
	pxor xmm7, xmm0
	pxor xmm4, xmm7
	pxor xmm3, xmm5
	movdqa xmm0, xmm2
	pxor xmm0, xmm5
	pxor xmm2, xmm7
	movdqu XMMWORD PTR [edi+416], xmm7
	movdqu xmm7, XMMWORD PTR [edi+448]
	pxor xmm7, xmm5
	movdqa xmm5, xmm7
	pxor xmm5, xmm2
	pxor xmm7, xmm1
	pxor xmm2, xmm6
	pxor xmm1, xmm6
	movdqu xmm6, XMMWORD PTR [edi+144]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [edi+304], xmm0
	movdqu xmm0, XMMWORD PTR [edi+336]
	pxor xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+224]
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pand xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+224]
	movdqu XMMWORD PTR [edi+336], xmm2
	movdqu xmm2, XMMWORD PTR [edi+320]
	pxor xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edi+144]
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu xmm1, XMMWORD PTR [edi+320]
	pxor xmm1, xmm6
	pxor xmm0, xmm4
	movdqu xmm6, XMMWORD PTR [edi+288]
	pxor xmm6, xmm2
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [edi+144], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pand xmm0, xmm4
	pxor xmm0, xmm6
	movdqa xmm4, xmm6
	pxor xmm4, xmm3
	movdqu XMMWORD PTR [edi+320], xmm0
	movdqu xmm0, XMMWORD PTR [ebx+48]
	pand xmm0, xmm4
	pxor xmm6, xmm5
	movdqa xmm4, xmm5
	pxor xmm4, xmm1
	movdqu XMMWORD PTR [edi+384], xmm1
	movdqu xmm1, XMMWORD PTR [edi+256]
	pxor xmm1, xmm4
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pand xmm4, xmm1
	movdqu xmm1, XMMWORD PTR [edi+256]
	movdqu XMMWORD PTR [edi+240], xmm6
	movdqu xmm6, XMMWORD PTR [edi+432]
	pxor xmm6, xmm1
	pxor xmm5, xmm6
	movdqu xmm1, XMMWORD PTR [edi+288]
	pxor xmm1, xmm5
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pand xmm5, xmm1
	pxor xmm2, xmm6
	pxor xmm6, xmm7
	pxor xmm3, xmm2
	pxor xmm3, xmm4
	movdqu xmm4, XMMWORD PTR [edi+208]
	movdqu xmm1, XMMWORD PTR [edi+288]
	pxor xmm1, xmm4
	pxor xmm6, xmm1
	pxor xmm6, xmm0
	movdqu xmm0, XMMWORD PTR [edi+448]
	pxor xmm0, xmm1
	pxor xmm4, xmm2
	movdqu xmm1, XMMWORD PTR [edi+224]
	pxor xmm1, xmm2
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pand xmm2, xmm1
	movdqu xmm1, XMMWORD PTR [edi+240]
	pxor xmm1, xmm2
	pxor xmm7, xmm4
	movdqu xmm2, XMMWORD PTR [ebx+48]
	pand xmm2, xmm7
	movdqu xmm7, XMMWORD PTR [edi+336]
	pxor xmm7, xmm4
	movdqu XMMWORD PTR [edi+336], xmm6
	movdqu xmm6, XMMWORD PTR [ebx+48]
	pand xmm6, xmm7
	movdqu xmm7, XMMWORD PTR [edi+304]
	pxor xmm7, xmm4
	pxor xmm7, xmm5
	movdqu xmm5, XMMWORD PTR [edi+384]
	pxor xmm5, xmm0
	movdqu xmm4, XMMWORD PTR [edi+416]
	pxor xmm4, xmm5
	movdqu xmm5, XMMWORD PTR [edi+432]
	pxor xmm5, xmm4
	pxor xmm5, xmm2
	movdqu xmm2, XMMWORD PTR [edi+352]
	pxor xmm2, xmm0
	movdqu xmm0, XMMWORD PTR [edi+160]
	pxor xmm0, xmm2
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+16], xmm1
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+80], xmm0
	movdqu XMMWORD PTR [edi+96], xmm7
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm0, XMMWORD PTR [edi+336]
	movdqu XMMWORD PTR [edi], xmm0
	movdqu xmm0, XMMWORD PTR [edi+144]
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi+320]
	movdqu XMMWORD PTR [edi+64], xmm0
	movdqu xmm6, XMMWORD PTR [ebx+32]
	movdqu xmm0, XMMWORD PTR [edi]
	pand xmm0, xmm6
	movdqu xmm4, XMMWORD PTR [edi+64]
	pand xmm4, xmm6
	pslld xmm4, 4
	pxor xmm0, xmm4
	movdqu xmm1, XMMWORD PTR [edi+16]
	pand xmm1, xmm6
	movdqu xmm4, XMMWORD PTR [edi+80]
	pand xmm4, xmm6
	pslld xmm4, 4
	pxor xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+32]
	pand xmm2, xmm6
	movdqu xmm4, XMMWORD PTR [edi+96]
	pand xmm4, xmm6
	pslld xmm4, 4
	pxor xmm2, xmm4
	movdqu xmm3, XMMWORD PTR [edi+48]
	pand xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+112]
	pand xmm4, xmm6
	pslld xmm4, 4
	pxor xmm3, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+16]
	movdqa xmm4, xmm0
	psrlq xmm4, 2
	pxor xmm4, xmm2
	pand xmm4, xmm6
	pxor xmm2, xmm4
	psllq xmm4, 2
	pxor xmm0, xmm4
	movdqa xmm4, xmm1
	psrlq xmm4, 2
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 2
	pxor xmm1, xmm4
	movdqu xmm6, XMMWORD PTR [ebx]
	movdqa xmm4, xmm0
	psrlq xmm4, 1
	pxor xmm4, xmm1
	pand xmm4, xmm6
	pxor xmm1, xmm4
	psllq xmm4, 1
	pxor xmm0, xmm4
	movdqa xmm4, xmm2
	psrlq xmm4, 1
	pxor xmm4, xmm3
	pand xmm4, xmm6
	pxor xmm3, xmm4
	psllq xmm4, 1
	pxor xmm2, xmm4
	movdqa xmm4, xmm0
	psrld xmm4, 8
	movdqa xmm5, xmm0
	pslld xmm5, 24
	pxor xmm4, xmm5
	movdqa xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pand xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pand xmm0, xmm6
	movdqa xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pand xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pand xmm7, xmm6
	pxor xmm0, xmm4
	pxor xmm5, xmm7
	pshuflw xmm5, xmm5, 177
	pshufhw xmm5, xmm5, 177
	pxor xmm0, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqa xmm4, xmm1
	psrld xmm4, 8
	movdqa xmm5, xmm1
	pslld xmm5, 24
	pxor xmm4, xmm5
	movdqa xmm5, xmm1
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pand xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pand xmm1, xmm6
	movdqa xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pand xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pand xmm7, xmm6
	pxor xmm1, xmm4
	pxor xmm5, xmm7
	pshuflw xmm5, xmm5, 177
	pshufhw xmm5, xmm5, 177
	pxor xmm1, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pxor xmm1, xmm6
	movdqu XMMWORD PTR [edi+528], xmm1
	movdqa xmm4, xmm2
	psrld xmm4, 8
	movdqa xmm5, xmm2
	pslld xmm5, 24
	pxor xmm4, xmm5
	movdqa xmm5, xmm2
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pand xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pand xmm2, xmm6
	movdqa xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pand xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pand xmm7, xmm6
	pxor xmm2, xmm4
	pxor xmm5, xmm7
	pshuflw xmm5, xmm5, 177
	pshufhw xmm5, xmm5, 177
	pxor xmm2, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+544], xmm2
	movdqa xmm4, xmm3
	psrld xmm4, 8
	movdqa xmm5, xmm3
	pslld xmm5, 24
	pxor xmm4, xmm5
	movdqa xmm5, xmm3
	movdqu xmm6, XMMWORD PTR [ebx+96]
	pand xmm5, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pand xmm3, xmm6
	movdqa xmm7, xmm4
	movdqu xmm6, XMMWORD PTR [ebx+80]
	pand xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [ebx+112]
	pand xmm7, xmm6
	pxor xmm3, xmm4
	pxor xmm5, xmm7
	pshuflw xmm5, xmm5, 177
	pshufhw xmm5, xmm5, 177
	pxor xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [ebx+128]
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+560], xmm3
	ret
	.p2align 6
