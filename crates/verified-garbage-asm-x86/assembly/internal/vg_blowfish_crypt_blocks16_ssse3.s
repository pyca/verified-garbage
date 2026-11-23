// The functions of `src/internal/vg_blowfish_crypt_blocks16_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_crypt_blocks16_ssse3:
	call 2f
2:
	mov eax, DWORD PTR [esp]
	.byte 0x81, 192
	.long {VG_BLOWFISH_SSSE3}
	pop ecx
	mov ebx, eax
	mov ebp, edx
	add ebp, 64
	movdqu xmm6, XMMWORD PTR [ebx+288]
	movdqu xmm7, XMMWORD PTR [ebx+304]
	movdqu xmm0, XMMWORD PTR [edi+384]
	movdqu xmm1, XMMWORD PTR [edi+400]
	movdqa xmm2, xmm0
	movdqa xmm3, xmm1
	pshufb xmm0, xmm6
	pshufb xmm1, xmm6
	punpcklqdq xmm0, xmm1
	pshufb xmm2, xmm7
	pshufb xmm3, xmm7
	punpcklqdq xmm2, xmm3
	movdqu XMMWORD PTR [edi+512], xmm0
	movdqu XMMWORD PTR [edi+576], xmm2
	movdqu xmm0, XMMWORD PTR [edi+416]
	movdqu xmm1, XMMWORD PTR [edi+432]
	movdqa xmm2, xmm0
	movdqa xmm3, xmm1
	pshufb xmm0, xmm6
	pshufb xmm1, xmm6
	punpcklqdq xmm0, xmm1
	pshufb xmm2, xmm7
	pshufb xmm3, xmm7
	punpcklqdq xmm2, xmm3
	movdqu XMMWORD PTR [edi+528], xmm0
	movdqu XMMWORD PTR [edi+592], xmm2
	movdqu xmm0, XMMWORD PTR [edi+448]
	movdqu xmm1, XMMWORD PTR [edi+464]
	movdqa xmm2, xmm0
	movdqa xmm3, xmm1
	pshufb xmm0, xmm6
	pshufb xmm1, xmm6
	punpcklqdq xmm0, xmm1
	pshufb xmm2, xmm7
	pshufb xmm3, xmm7
	punpcklqdq xmm2, xmm3
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu XMMWORD PTR [edi+608], xmm2
	movdqu xmm0, XMMWORD PTR [edi+480]
	movdqu xmm1, XMMWORD PTR [edi+496]
	movdqa xmm2, xmm0
	movdqa xmm3, xmm1
	pshufb xmm0, xmm6
	pshufb xmm1, xmm6
	punpcklqdq xmm0, xmm1
	pshufb xmm2, xmm7
	pshufb xmm3, xmm7
	punpcklqdq xmm2, xmm3
	movdqu XMMWORD PTR [edi+560], xmm0
	movdqu XMMWORD PTR [edi+624], xmm2
20:
	mov eax, DWORD PTR [edx]
	movd xmm4, eax
	pshufd xmm4, xmm4, 0
	movdqu xmm5, XMMWORD PTR [ebx+256]
	movdqu xmm0, XMMWORD PTR [edi+512]
	pxor xmm0, xmm4
	movdqu XMMWORD PTR [edi+640], xmm0
	pshufb xmm0, xmm5
	movdqu xmm1, XMMWORD PTR [edi+528]
	pxor xmm1, xmm4
	movdqu XMMWORD PTR [edi+656], xmm1
	pshufb xmm1, xmm5
	movdqu xmm2, XMMWORD PTR [edi+544]
	pxor xmm2, xmm4
	movdqu XMMWORD PTR [edi+672], xmm2
	pshufb xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+560]
	pxor xmm3, xmm4
	movdqu XMMWORD PTR [edi+688], xmm3
	pshufb xmm3, xmm5
	movdqa xmm4, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm4, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm2, xmm3
	punpckhdq xmm5, xmm3
	movdqa xmm6, xmm0
	punpcklqdq xmm0, xmm2
	punpckhqdq xmm6, xmm2
	movdqa xmm7, xmm4
	punpcklqdq xmm4, xmm5
	punpckhqdq xmm7, xmm5
	movdqu XMMWORD PTR [edi+704], xmm0
	movdqu XMMWORD PTR [edi+720], xmm6
	movdqu XMMWORD PTR [edi+736], xmm4
	movdqu XMMWORD PTR [edi+752], xmm7
	movdqu xmm0, XMMWORD PTR [edi+752]
	movdqu xmm2, XMMWORD PTR [ebx+272]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm2
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+80], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+80]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+144], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+176]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+240], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+256], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+272], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+288], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+304], xmm5
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [esi]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [esi+256]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [esi+512]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [esi+768]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [esi+16]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+272]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+528]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+784]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [esi+32]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+288]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+544]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+800]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+112]
	movdqu xmm0, XMMWORD PTR [esi+48]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+304]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+560]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+816]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [esi+64]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+320]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+576]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+832]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+144]
	movdqu xmm2, XMMWORD PTR [esi+80]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+336]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+592]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+848]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+160]
	movdqu xmm7, XMMWORD PTR [esi+96]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+352]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+608]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+864]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm4, XMMWORD PTR [esi+112]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+368]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+624]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+880]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edi+192]
	movdqu xmm1, XMMWORD PTR [esi+128]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+384]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+640]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+896]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+208]
	movdqu xmm6, XMMWORD PTR [esi+144]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+400]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+656]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+912]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [esi+160]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+416]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+672]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+928]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+240]
	movdqu xmm0, XMMWORD PTR [esi+176]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+432]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+688]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+944]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+256]
	movdqu xmm5, XMMWORD PTR [esi+192]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+448]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+704]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+960]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+272]
	movdqu xmm2, XMMWORD PTR [esi+208]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+464]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+720]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+976]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+288]
	movdqu xmm7, XMMWORD PTR [esi+224]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+480]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+736]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+992]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+304]
	movdqu xmm4, XMMWORD PTR [esi+240]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+496]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+752]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+1008]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu XMMWORD PTR [edi+320], xmm4
	movdqu XMMWORD PTR [edi+336], xmm2
	movdqu XMMWORD PTR [edi+352], xmm0
	movdqu XMMWORD PTR [edi+368], xmm3
	movdqu xmm0, XMMWORD PTR [edi+736]
	movdqu xmm2, XMMWORD PTR [ebx+272]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm2
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+80], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+80]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+144], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+176]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+240], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+256], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+272], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+288], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+304], xmm5
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [esi+1024]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [esi+1280]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [esi+1536]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [esi+1792]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [esi+1040]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+1296]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+1552]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+1808]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [esi+1056]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+1312]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+1568]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+1824]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+112]
	movdqu xmm0, XMMWORD PTR [esi+1072]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+1328]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+1584]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+1840]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [esi+1088]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+1344]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+1600]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+1856]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+144]
	movdqu xmm2, XMMWORD PTR [esi+1104]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+1360]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+1616]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+1872]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+160]
	movdqu xmm7, XMMWORD PTR [esi+1120]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+1376]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+1632]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+1888]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm4, XMMWORD PTR [esi+1136]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+1392]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+1648]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+1904]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edi+192]
	movdqu xmm1, XMMWORD PTR [esi+1152]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+1408]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+1664]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+1920]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+208]
	movdqu xmm6, XMMWORD PTR [esi+1168]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+1424]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+1680]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+1936]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [esi+1184]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+1440]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+1696]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+1952]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+240]
	movdqu xmm0, XMMWORD PTR [esi+1200]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+1456]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+1712]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+1968]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+256]
	movdqu xmm5, XMMWORD PTR [esi+1216]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+1472]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+1728]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+1984]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+272]
	movdqu xmm2, XMMWORD PTR [esi+1232]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+1488]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+1744]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+2000]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+288]
	movdqu xmm7, XMMWORD PTR [esi+1248]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+1504]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+1760]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+2016]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+304]
	movdqu xmm4, XMMWORD PTR [esi+1264]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+1520]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+1776]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+2032]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [edi+320]
	paddd xmm4, xmm6
	movdqu XMMWORD PTR [edi+320], xmm4
	movdqu xmm6, XMMWORD PTR [edi+336]
	paddd xmm2, xmm6
	movdqu XMMWORD PTR [edi+336], xmm2
	movdqu xmm6, XMMWORD PTR [edi+352]
	paddd xmm0, xmm6
	movdqu XMMWORD PTR [edi+352], xmm0
	movdqu xmm6, XMMWORD PTR [edi+368]
	paddd xmm3, xmm6
	movdqu XMMWORD PTR [edi+368], xmm3
	movdqu xmm0, XMMWORD PTR [edi+720]
	movdqu xmm2, XMMWORD PTR [ebx+272]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm2
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+80], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+80]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+144], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+176]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+240], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+256], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+272], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+288], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+304], xmm5
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [esi+2048]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [esi+2304]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [esi+2560]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [esi+2816]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [esi+2064]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+2320]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+2576]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+2832]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [esi+2080]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+2336]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+2592]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+2848]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+112]
	movdqu xmm0, XMMWORD PTR [esi+2096]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+2352]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+2608]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+2864]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [esi+2112]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+2368]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+2624]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+2880]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+144]
	movdqu xmm2, XMMWORD PTR [esi+2128]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+2384]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+2640]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+2896]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+160]
	movdqu xmm7, XMMWORD PTR [esi+2144]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+2400]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+2656]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+2912]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm4, XMMWORD PTR [esi+2160]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+2416]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+2672]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+2928]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edi+192]
	movdqu xmm1, XMMWORD PTR [esi+2176]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+2432]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+2688]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+2944]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+208]
	movdqu xmm6, XMMWORD PTR [esi+2192]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+2448]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+2704]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+2960]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [esi+2208]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+2464]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+2720]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+2976]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+240]
	movdqu xmm0, XMMWORD PTR [esi+2224]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+2480]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+2736]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+2992]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+256]
	movdqu xmm5, XMMWORD PTR [esi+2240]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+2496]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+2752]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+3008]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+272]
	movdqu xmm2, XMMWORD PTR [esi+2256]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+2512]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+2768]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+3024]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+288]
	movdqu xmm7, XMMWORD PTR [esi+2272]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+2528]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+2784]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+3040]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+304]
	movdqu xmm4, XMMWORD PTR [esi+2288]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+2544]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+2800]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+3056]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [edi+320]
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [edi+320], xmm4
	movdqu xmm6, XMMWORD PTR [edi+336]
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+336], xmm2
	movdqu xmm6, XMMWORD PTR [edi+352]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+352], xmm0
	movdqu xmm6, XMMWORD PTR [edi+368]
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+368], xmm3
	movdqu xmm0, XMMWORD PTR [edi+704]
	movdqu xmm2, XMMWORD PTR [ebx+272]
	movdqa xmm1, xmm0
	psrld xmm1, 4
	pand xmm1, xmm2
	pand xmm0, xmm2
	movdqu xmm2, XMMWORD PTR [ebx]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+16]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+80], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+96], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+48]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+112], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+64]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+128], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+80]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+144], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+96]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+160], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+112]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+128]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+192], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+144]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm6, XMMWORD PTR [ebx+160]
	pshufb xmm6, xmm1
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+224], xmm6
	movdqu xmm7, XMMWORD PTR [ebx+176]
	pshufb xmm7, xmm1
	por xmm7, xmm0
	movdqu XMMWORD PTR [edi+240], xmm7
	movdqu xmm2, XMMWORD PTR [ebx+192]
	pshufb xmm2, xmm1
	por xmm2, xmm0
	movdqu XMMWORD PTR [edi+256], xmm2
	movdqu xmm3, XMMWORD PTR [ebx+208]
	pshufb xmm3, xmm1
	por xmm3, xmm0
	movdqu XMMWORD PTR [edi+272], xmm3
	movdqu xmm4, XMMWORD PTR [ebx+224]
	pshufb xmm4, xmm1
	por xmm4, xmm0
	movdqu XMMWORD PTR [edi+288], xmm4
	movdqu xmm5, XMMWORD PTR [ebx+240]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu XMMWORD PTR [edi+304], xmm5
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [esi+3072]
	pshufb xmm1, xmm0
	movdqu xmm2, XMMWORD PTR [esi+3328]
	pshufb xmm2, xmm0
	movdqu xmm3, XMMWORD PTR [esi+3584]
	pshufb xmm3, xmm0
	movdqu xmm4, XMMWORD PTR [esi+3840]
	pshufb xmm4, xmm0
	movdqu xmm5, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [esi+3088]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+3344]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+3600]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+3856]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [esi+3104]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+3360]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+3616]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+3872]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+112]
	movdqu xmm0, XMMWORD PTR [esi+3120]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+3376]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+3632]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+3888]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [esi+3136]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+3392]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+3648]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+3904]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+144]
	movdqu xmm2, XMMWORD PTR [esi+3152]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+3408]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+3664]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+3920]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+160]
	movdqu xmm7, XMMWORD PTR [esi+3168]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+3424]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+3680]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+3936]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm4, XMMWORD PTR [esi+3184]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+3440]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+3696]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+3952]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [edi+192]
	movdqu xmm1, XMMWORD PTR [esi+3200]
	pshufb xmm1, xmm0
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+3456]
	pshufb xmm2, xmm0
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+3712]
	pshufb xmm3, xmm0
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+3968]
	pshufb xmm4, xmm0
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [edi+208]
	movdqu xmm6, XMMWORD PTR [esi+3216]
	pshufb xmm6, xmm5
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+3472]
	pshufb xmm7, xmm5
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+3728]
	pshufb xmm0, xmm5
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+3984]
	pshufb xmm1, xmm5
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [esi+3232]
	pshufb xmm3, xmm2
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+3488]
	pshufb xmm4, xmm2
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+3744]
	pshufb xmm5, xmm2
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+4000]
	pshufb xmm6, xmm2
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [edi+240]
	movdqu xmm0, XMMWORD PTR [esi+3248]
	pshufb xmm0, xmm7
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+3504]
	pshufb xmm1, xmm7
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+3760]
	pshufb xmm2, xmm7
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+4016]
	pshufb xmm3, xmm7
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [edi+256]
	movdqu xmm5, XMMWORD PTR [esi+3264]
	pshufb xmm5, xmm4
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+3520]
	pshufb xmm6, xmm4
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+3776]
	pshufb xmm7, xmm4
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+4032]
	pshufb xmm0, xmm4
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [edi+272]
	movdqu xmm2, XMMWORD PTR [esi+3280]
	pshufb xmm2, xmm1
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [esi+3536]
	pshufb xmm3, xmm1
	por xmm3, xmm6
	movdqu xmm4, XMMWORD PTR [esi+3792]
	pshufb xmm4, xmm1
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+4048]
	pshufb xmm5, xmm1
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [edi+288]
	movdqu xmm7, XMMWORD PTR [esi+3296]
	pshufb xmm7, xmm6
	por xmm7, xmm2
	movdqu xmm0, XMMWORD PTR [esi+3552]
	pshufb xmm0, xmm6
	por xmm0, xmm3
	movdqu xmm1, XMMWORD PTR [esi+3808]
	pshufb xmm1, xmm6
	por xmm1, xmm4
	movdqu xmm2, XMMWORD PTR [esi+4064]
	pshufb xmm2, xmm6
	por xmm2, xmm5
	movdqu xmm3, XMMWORD PTR [edi+304]
	movdqu xmm4, XMMWORD PTR [esi+3312]
	pshufb xmm4, xmm3
	por xmm4, xmm7
	movdqu xmm5, XMMWORD PTR [esi+3568]
	pshufb xmm5, xmm3
	por xmm5, xmm0
	movdqu xmm6, XMMWORD PTR [esi+3824]
	pshufb xmm6, xmm3
	por xmm6, xmm1
	movdqu xmm7, XMMWORD PTR [esi+4080]
	pshufb xmm7, xmm3
	por xmm7, xmm2
	movdqa xmm0, xmm4
	punpckldq xmm4, xmm5
	punpckhdq xmm0, xmm5
	movdqa xmm1, xmm6
	punpckldq xmm6, xmm7
	punpckhdq xmm1, xmm7
	movdqa xmm2, xmm4
	punpcklqdq xmm4, xmm6
	punpckhqdq xmm2, xmm6
	movdqa xmm3, xmm0
	punpcklqdq xmm0, xmm1
	punpckhqdq xmm3, xmm1
	movdqu xmm5, XMMWORD PTR [ebx+256]
	pshufb xmm4, xmm5
	pshufb xmm2, xmm5
	pshufb xmm0, xmm5
	pshufb xmm3, xmm5
	movdqu xmm6, XMMWORD PTR [edi+320]
	paddd xmm4, xmm6
	movdqu xmm6, XMMWORD PTR [edi+576]
	pxor xmm4, xmm6
	movdqu XMMWORD PTR [edi+512], xmm4
	movdqu xmm6, XMMWORD PTR [edi+336]
	paddd xmm2, xmm6
	movdqu xmm6, XMMWORD PTR [edi+592]
	pxor xmm2, xmm6
	movdqu XMMWORD PTR [edi+528], xmm2
	movdqu xmm6, XMMWORD PTR [edi+352]
	paddd xmm0, xmm6
	movdqu xmm6, XMMWORD PTR [edi+608]
	pxor xmm0, xmm6
	movdqu XMMWORD PTR [edi+544], xmm0
	movdqu xmm6, XMMWORD PTR [edi+368]
	paddd xmm3, xmm6
	movdqu xmm6, XMMWORD PTR [edi+624]
	pxor xmm3, xmm6
	movdqu XMMWORD PTR [edi+560], xmm3
	movdqu xmm0, XMMWORD PTR [edi+640]
	movdqu XMMWORD PTR [edi+576], xmm0
	movdqu xmm0, XMMWORD PTR [edi+656]
	movdqu XMMWORD PTR [edi+592], xmm0
	movdqu xmm0, XMMWORD PTR [edi+672]
	movdqu XMMWORD PTR [edi+608], xmm0
	movdqu xmm0, XMMWORD PTR [edi+688]
	movdqu XMMWORD PTR [edi+624], xmm0
	add edx, 4
	cmp edx, ebp
	jne 20b
	mov eax, DWORD PTR [edx]
	mov ecx, DWORD PTR [edx+4]
	movd xmm6, eax
	pshufd xmm6, xmm6, 0
	movd xmm7, ecx
	pshufd xmm7, xmm7, 0
	movdqu xmm5, XMMWORD PTR [ebx+320]
	movdqu xmm0, XMMWORD PTR [edi+576]
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+512]
	pxor xmm1, xmm6
	movdqa xmm2, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm2, xmm1
	pshufb xmm0, xmm5
	pshufb xmm2, xmm5
	movdqu XMMWORD PTR [edi+384], xmm0
	movdqu XMMWORD PTR [edi+400], xmm2
	movdqu xmm0, XMMWORD PTR [edi+592]
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+528]
	pxor xmm1, xmm6
	movdqa xmm2, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm2, xmm1
	pshufb xmm0, xmm5
	pshufb xmm2, xmm5
	movdqu XMMWORD PTR [edi+416], xmm0
	movdqu XMMWORD PTR [edi+432], xmm2
	movdqu xmm0, XMMWORD PTR [edi+608]
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+544]
	pxor xmm1, xmm6
	movdqa xmm2, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm2, xmm1
	pshufb xmm0, xmm5
	pshufb xmm2, xmm5
	movdqu XMMWORD PTR [edi+448], xmm0
	movdqu XMMWORD PTR [edi+464], xmm2
	movdqu xmm0, XMMWORD PTR [edi+624]
	pxor xmm0, xmm7
	movdqu xmm1, XMMWORD PTR [edi+560]
	pxor xmm1, xmm6
	movdqa xmm2, xmm0
	punpckldq xmm0, xmm1
	punpckhdq xmm2, xmm1
	pshufb xmm0, xmm5
	pshufb xmm2, xmm5
	movdqu XMMWORD PTR [edi+480], xmm0
	movdqu XMMWORD PTR [edi+496], xmm2
	ret
	.p2align 6
