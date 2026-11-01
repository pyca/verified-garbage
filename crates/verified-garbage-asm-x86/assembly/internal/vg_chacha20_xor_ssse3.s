// The functions of `src/internal/vg_chacha20_xor_ssse3.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_ssse3:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+256], ebx
	mov DWORD PTR [eax+260], esi
	mov DWORD PTR [eax+264], edi
	mov DWORD PTR [eax+268], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
	mov eax, 16777986
	mov DWORD PTR [edi+288], eax
	mov eax, 84150022
	mov DWORD PTR [edi+292], eax
	mov eax, 151522058
	mov DWORD PTR [edi+296], eax
	mov eax, 218894094
	mov DWORD PTR [edi+300], eax
	mov eax, 33619971
	mov DWORD PTR [edi+304], eax
	mov eax, 100992007
	mov DWORD PTR [edi+308], eax
	mov eax, 168364043
	mov DWORD PTR [edi+312], eax
	mov eax, 235736079
	mov DWORD PTR [edi+316], eax
	cmp ebp, 65
	jb 20f
22:
	movdqu xmm4, XMMWORD PTR [ebx]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [edi], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [edi+16], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [edi+32], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [edi+48], xmm0
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [edi+64], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [edi+80], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [edi+96], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [edi+112], xmm0
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [edi+128], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [edi+144], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [edi+160], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [edi+176], xmm0
	movdqu xmm4, XMMWORD PTR [ebx+48]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [edi+192], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [edi+208], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [edi+224], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [edi+240], xmm0
	mov eax, DWORD PTR [ebx+48]
	mov DWORD PTR [edi+192], eax
	mov DWORD PTR [edi+272], eax
	add eax, 1
	mov DWORD PTR [edi+196], eax
	mov DWORD PTR [edi+276], eax
	add eax, 1
	mov DWORD PTR [edi+200], eax
	mov DWORD PTR [edi+280], eax
	add eax, 1
	mov DWORD PTR [edi+204], eax
	mov DWORD PTR [edi+284], eax
	add eax, 1
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm1, XMMWORD PTR [edi+48]
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm6, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm0, xmm2
	pxor xmm6, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm4, xmm6
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm6, XMMWORD PTR [edi+208]
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm6, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+208], xmm6
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+160]
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 12
	psrld xmm7, 20
	por xmm3, xmm7
	paddd xmm2, xmm3
	pxor xmm5, xmm2
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm3, xmm6
	movdqa xmm7, xmm3
	pslld xmm3, 7
	psrld xmm7, 25
	por xmm3, xmm7
	movdqu XMMWORD PTR [edi+32], xmm2
	movdqu XMMWORD PTR [edi+96], xmm3
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm2, XMMWORD PTR [edi+112]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm5, XMMWORD PTR [edi+240]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm0, xmm4
	pxor xmm5, xmm0
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm6, xmm5
	pxor xmm4, xmm6
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu XMMWORD PTR [edi+160], xmm6
	movdqu XMMWORD PTR [edi+240], xmm5
	movdqu xmm4, XMMWORD PTR [edi+16]
	movdqu xmm5, XMMWORD PTR [edi+96]
	movdqu xmm6, XMMWORD PTR [edi+192]
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 12
	psrld xmm7, 20
	por xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm6, xmm4
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm6, xmm7
	paddd xmm3, xmm6
	pxor xmm5, xmm3
	movdqa xmm7, xmm5
	pslld xmm5, 7
	psrld xmm7, 25
	por xmm5, xmm7
	movdqu XMMWORD PTR [edi+16], xmm4
	movdqu XMMWORD PTR [edi+96], xmm5
	movdqu XMMWORD PTR [edi+176], xmm3
	movdqu xmm3, XMMWORD PTR [edi+32]
	movdqu xmm4, XMMWORD PTR [edi+128]
	movdqu xmm5, XMMWORD PTR [edi+208]
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm3, xmm2
	pxor xmm5, xmm3
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm4, xmm5
	pxor xmm2, xmm4
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi+32], xmm3
	movdqu XMMWORD PTR [edi+112], xmm2
	movdqu XMMWORD PTR [edi+208], xmm5
	movdqu xmm2, XMMWORD PTR [edi+64]
	movdqu xmm3, XMMWORD PTR [edi+144]
	movdqu xmm5, XMMWORD PTR [edi+224]
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+288]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 12
	psrld xmm7, 20
	por xmm2, xmm7
	paddd xmm1, xmm2
	pxor xmm5, xmm1
	movdqu xmm7, XMMWORD PTR [edi+304]
	pshufb xmm5, xmm7
	paddd xmm3, xmm5
	pxor xmm2, xmm3
	movdqa xmm7, xmm2
	pslld xmm2, 7
	psrld xmm7, 25
	por xmm2, xmm7
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+48], xmm1
	movdqu XMMWORD PTR [edi+64], xmm2
	movdqu XMMWORD PTR [edi+128], xmm4
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu XMMWORD PTR [edi+192], xmm6
	movdqu XMMWORD PTR [edi+224], xmm5
	movdqu xmm0, XMMWORD PTR [edi]
	movdqu xmm1, XMMWORD PTR [edi+16]
	movdqu xmm2, XMMWORD PTR [edi+32]
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [ebx]
	pshufd xmm5, xmm4, 0
	paddd xmm0, xmm5
	pshufd xmm5, xmm4, 85
	paddd xmm1, xmm5
	pshufd xmm5, xmm4, 170
	paddd xmm2, xmm5
	pshufd xmm5, xmm4, 255
	paddd xmm3, xmm5
	movdqa xmm4, xmm0
	punpckldq xmm4, xmm1
	punpckhdq xmm0, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm5, xmm3
	punpckhdq xmm2, xmm3
	movdqa xmm1, xmm4
	punpcklqdq xmm1, xmm5
	punpckhqdq xmm4, xmm5
	movdqa xmm3, xmm0
	punpcklqdq xmm3, xmm2
	punpckhqdq xmm0, xmm2
	cmp ebp, 16
	jb 23f
	movdqu xmm6, XMMWORD PTR [esi]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [esi], xmm6
	jmp 24f
23:
	cmp ebp, 1
	jb 25f
	movdqu XMMWORD PTR [edi], xmm1
	jmp 26f
25:
26:
24:
	cmp ebp, 80
	jb 27f
	movdqu xmm6, XMMWORD PTR [esi+64]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [esi+64], xmm6
	jmp 28f
27:
	cmp ebp, 65
	jb 29f
	movdqu XMMWORD PTR [edi], xmm4
	jmp 210f
29:
210:
28:
	cmp ebp, 144
	jb 211f
	movdqu xmm6, XMMWORD PTR [esi+128]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [esi+128], xmm6
	jmp 212f
211:
	cmp ebp, 129
	jb 213f
	movdqu XMMWORD PTR [edi], xmm3
	jmp 214f
213:
214:
212:
	cmp ebp, 208
	jb 215f
	movdqu xmm6, XMMWORD PTR [esi+192]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [esi+192], xmm6
	jmp 216f
215:
	cmp ebp, 193
	jb 217f
	movdqu XMMWORD PTR [edi], xmm0
	jmp 218f
217:
218:
216:
	movdqu xmm0, XMMWORD PTR [edi+64]
	movdqu xmm1, XMMWORD PTR [edi+80]
	movdqu xmm2, XMMWORD PTR [edi+96]
	movdqu xmm3, XMMWORD PTR [edi+112]
	movdqu xmm4, XMMWORD PTR [ebx+16]
	pshufd xmm5, xmm4, 0
	paddd xmm0, xmm5
	pshufd xmm5, xmm4, 85
	paddd xmm1, xmm5
	pshufd xmm5, xmm4, 170
	paddd xmm2, xmm5
	pshufd xmm5, xmm4, 255
	paddd xmm3, xmm5
	movdqa xmm4, xmm0
	punpckldq xmm4, xmm1
	punpckhdq xmm0, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm5, xmm3
	punpckhdq xmm2, xmm3
	movdqa xmm1, xmm4
	punpcklqdq xmm1, xmm5
	punpckhqdq xmm4, xmm5
	movdqa xmm3, xmm0
	punpcklqdq xmm3, xmm2
	punpckhqdq xmm0, xmm2
	cmp ebp, 32
	jb 219f
	movdqu xmm6, XMMWORD PTR [esi+16]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [esi+16], xmm6
	jmp 220f
219:
	cmp ebp, 17
	jb 221f
	movdqu XMMWORD PTR [edi], xmm1
	jmp 222f
221:
222:
220:
	cmp ebp, 96
	jb 223f
	movdqu xmm6, XMMWORD PTR [esi+80]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [esi+80], xmm6
	jmp 224f
223:
	cmp ebp, 81
	jb 225f
	movdqu XMMWORD PTR [edi], xmm4
	jmp 226f
225:
226:
224:
	cmp ebp, 160
	jb 227f
	movdqu xmm6, XMMWORD PTR [esi+144]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [esi+144], xmm6
	jmp 228f
227:
	cmp ebp, 145
	jb 229f
	movdqu XMMWORD PTR [edi], xmm3
	jmp 230f
229:
230:
228:
	cmp ebp, 224
	jb 231f
	movdqu xmm6, XMMWORD PTR [esi+208]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [esi+208], xmm6
	jmp 232f
231:
	cmp ebp, 209
	jb 233f
	movdqu XMMWORD PTR [edi], xmm0
	jmp 234f
233:
234:
232:
	movdqu xmm0, XMMWORD PTR [edi+128]
	movdqu xmm1, XMMWORD PTR [edi+144]
	movdqu xmm2, XMMWORD PTR [edi+160]
	movdqu xmm3, XMMWORD PTR [edi+176]
	movdqu xmm4, XMMWORD PTR [ebx+32]
	pshufd xmm5, xmm4, 0
	paddd xmm0, xmm5
	pshufd xmm5, xmm4, 85
	paddd xmm1, xmm5
	pshufd xmm5, xmm4, 170
	paddd xmm2, xmm5
	pshufd xmm5, xmm4, 255
	paddd xmm3, xmm5
	movdqa xmm4, xmm0
	punpckldq xmm4, xmm1
	punpckhdq xmm0, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm5, xmm3
	punpckhdq xmm2, xmm3
	movdqa xmm1, xmm4
	punpcklqdq xmm1, xmm5
	punpckhqdq xmm4, xmm5
	movdqa xmm3, xmm0
	punpcklqdq xmm3, xmm2
	punpckhqdq xmm0, xmm2
	cmp ebp, 48
	jb 235f
	movdqu xmm6, XMMWORD PTR [esi+32]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [esi+32], xmm6
	jmp 236f
235:
	cmp ebp, 33
	jb 237f
	movdqu XMMWORD PTR [edi], xmm1
	jmp 238f
237:
238:
236:
	cmp ebp, 112
	jb 239f
	movdqu xmm6, XMMWORD PTR [esi+96]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [esi+96], xmm6
	jmp 240f
239:
	cmp ebp, 97
	jb 241f
	movdqu XMMWORD PTR [edi], xmm4
	jmp 242f
241:
242:
240:
	cmp ebp, 176
	jb 243f
	movdqu xmm6, XMMWORD PTR [esi+160]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [esi+160], xmm6
	jmp 244f
243:
	cmp ebp, 161
	jb 245f
	movdqu XMMWORD PTR [edi], xmm3
	jmp 246f
245:
246:
244:
	cmp ebp, 240
	jb 247f
	movdqu xmm6, XMMWORD PTR [esi+224]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [esi+224], xmm6
	jmp 248f
247:
	cmp ebp, 225
	jb 249f
	movdqu XMMWORD PTR [edi], xmm0
	jmp 250f
249:
250:
248:
	movdqu xmm0, XMMWORD PTR [edi+192]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm2, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+240]
	movdqu xmm4, XMMWORD PTR [ebx+48]
	movdqu xmm5, XMMWORD PTR [edi+272]
	paddd xmm0, xmm5
	pshufd xmm5, xmm4, 85
	paddd xmm1, xmm5
	pshufd xmm5, xmm4, 170
	paddd xmm2, xmm5
	pshufd xmm5, xmm4, 255
	paddd xmm3, xmm5
	movdqa xmm4, xmm0
	punpckldq xmm4, xmm1
	punpckhdq xmm0, xmm1
	movdqa xmm5, xmm2
	punpckldq xmm5, xmm3
	punpckhdq xmm2, xmm3
	movdqa xmm1, xmm4
	punpcklqdq xmm1, xmm5
	punpckhqdq xmm4, xmm5
	movdqa xmm3, xmm0
	punpcklqdq xmm3, xmm2
	punpckhqdq xmm0, xmm2
	cmp ebp, 64
	jb 251f
	movdqu xmm6, XMMWORD PTR [esi+48]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [esi+48], xmm6
	jmp 252f
251:
	cmp ebp, 49
	jb 253f
	movdqu XMMWORD PTR [edi], xmm1
	jmp 254f
253:
254:
252:
	cmp ebp, 128
	jb 255f
	movdqu xmm6, XMMWORD PTR [esi+112]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [esi+112], xmm6
	jmp 256f
255:
	cmp ebp, 113
	jb 257f
	movdqu XMMWORD PTR [edi], xmm4
	jmp 258f
257:
258:
256:
	cmp ebp, 192
	jb 259f
	movdqu xmm6, XMMWORD PTR [esi+176]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [esi+176], xmm6
	jmp 260f
259:
	cmp ebp, 177
	jb 261f
	movdqu XMMWORD PTR [edi], xmm3
	jmp 262f
261:
262:
260:
	cmp ebp, 256
	jb 263f
	movdqu xmm6, XMMWORD PTR [esi+240]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [esi+240], xmm6
	jmp 264f
263:
	cmp ebp, 241
	jb 265f
	movdqu XMMWORD PTR [edi], xmm0
	jmp 266f
265:
266:
264:
	cmp ebp, 257
	jb 267f
	mov eax, DWORD PTR [ebx+48]
	add eax, 4
	mov DWORD PTR [ebx+48], eax
	add esi, 256
	sub ebp, 256
	jmp 268f
267:
	mov ecx, ebp
	and ecx, 15
	and ebp, -16
	add esi, ebp
	mov edx, edi
	mov ebp, 0
	test ecx, ecx
	je 269f
271:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [edx]
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 271b
	jmp 270f
269:
270:
268:
	cmp ebp, 65
	jae 22b
	jmp 21f
20:
21:
	test ebp, ebp
	je 272f
	push edi
	push ebx
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov edx, edi
	mov ecx, ebp
	cmp ecx, 16
	jb 274f
276:
	movdqu xmm4, XMMWORD PTR [esi]
	movdqu xmm5, XMMWORD PTR [edx]
	pxor xmm4, xmm5
	movdqu XMMWORD PTR [esi], xmm4
	add esi, 16
	add edx, 16
	sub ecx, 16
	cmp ecx, 16
	jae 276b
	jmp 275f
274:
275:
	test ecx, ecx
	je 277f
279:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [edx]
	mov BYTE PTR [esi], al
	add esi, 1
	add edx, 1
	sub ecx, 1
	jne 279b
	jmp 278f
277:
278:
	jmp 273f
272:
273:
	mov eax, edi
	mov ebx, DWORD PTR [eax+256]
	mov esi, DWORD PTR [eax+260]
	mov edi, DWORD PTR [eax+264]
	mov ebp, DWORD PTR [eax+268]
	ret
	.p2align 6
