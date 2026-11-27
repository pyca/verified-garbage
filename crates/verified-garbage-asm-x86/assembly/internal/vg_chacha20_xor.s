// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax+256], ebx
	mov DWORD PTR [eax+260], esi
	mov DWORD PTR [eax+264], edi
	mov DWORD PTR [eax+268], ebp
	mov edx, esi
	mov edi, eax
	mov ebx, DWORD PTR [esp+4]
	mov esi, DWORD PTR [esp+8]
	mov ebp, DWORD PTR [esp+12]
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
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm5, XMMWORD PTR [edi+128]
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu xmm0, XMMWORD PTR [edi]
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 12
	psrld xmm2, 20
	por xmm4, xmm2
	paddd xmm0, xmm4
	pxor xmm7, xmm0
	movdqa xmm2, xmm7
	pslld xmm7, 8
	psrld xmm2, 24
	por xmm7, xmm2
	paddd xmm5, xmm7
	pxor xmm4, xmm5
	movdqa xmm2, xmm4
	pslld xmm4, 7
	psrld xmm2, 25
	por xmm4, xmm2
	movdqu XMMWORD PTR [edi], xmm0
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu xmm0, XMMWORD PTR [edi+240]
	movdqu xmm7, XMMWORD PTR [edi+176]
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 12
	psrld xmm5, 20
	por xmm6, xmm5
	paddd xmm3, xmm6
	pxor xmm0, xmm3
	movdqa xmm5, xmm0
	pslld xmm0, 8
	psrld xmm5, 24
	por xmm0, xmm5
	paddd xmm7, xmm0
	pxor xmm6, xmm7
	movdqa xmm5, xmm6
	pslld xmm6, 7
	psrld xmm5, 25
	por xmm6, xmm5
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+176], xmm7
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu xmm2, XMMWORD PTR [edi+16]
	movdqu xmm4, XMMWORD PTR [edi+80]
	movdqu xmm3, XMMWORD PTR [edi+144]
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm2, xmm4
	pxor xmm1, xmm2
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
	movdqu XMMWORD PTR [edi+144], xmm3
	movdqu xmm5, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+96]
	movdqu xmm1, XMMWORD PTR [edi+224]
	movdqu xmm3, XMMWORD PTR [edi+160]
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 12
	psrld xmm7, 20
	por xmm6, xmm7
	paddd xmm5, xmm6
	pxor xmm1, xmm5
	movdqa xmm7, xmm1
	pslld xmm1, 8
	psrld xmm7, 24
	por xmm1, xmm7
	paddd xmm3, xmm1
	pxor xmm6, xmm3
	movdqa xmm7, xmm6
	pslld xmm6, 7
	psrld xmm7, 25
	por xmm6, xmm7
	movdqu XMMWORD PTR [edi+32], xmm5
	movdqu xmm5, XMMWORD PTR [edi]
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	pshuflw xmm0, xmm0, 177
	pshufhw xmm0, xmm0, 177
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 12
	psrld xmm7, 20
	por xmm4, xmm7
	paddd xmm5, xmm4
	pxor xmm0, xmm5
	movdqa xmm7, xmm0
	pslld xmm0, 8
	psrld xmm7, 24
	por xmm0, xmm7
	paddd xmm3, xmm0
	pxor xmm4, xmm3
	movdqa xmm7, xmm4
	pslld xmm4, 7
	psrld xmm7, 25
	por xmm4, xmm7
	movdqu XMMWORD PTR [edi], xmm5
	movdqu XMMWORD PTR [edi+240], xmm0
	movdqu XMMWORD PTR [edi+160], xmm3
	movdqu XMMWORD PTR [edi+80], xmm4
	movdqu xmm7, XMMWORD PTR [edi+192]
	movdqu xmm5, XMMWORD PTR [edi+176]
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	pshuflw xmm7, xmm7, 177
	pshufhw xmm7, xmm7, 177
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 12
	psrld xmm0, 20
	por xmm6, xmm0
	paddd xmm2, xmm6
	pxor xmm7, xmm2
	movdqa xmm0, xmm7
	pslld xmm7, 8
	psrld xmm0, 24
	por xmm7, xmm0
	paddd xmm5, xmm7
	pxor xmm6, xmm5
	movdqa xmm0, xmm6
	pslld xmm6, 7
	psrld xmm0, 25
	por xmm6, xmm0
	movdqu XMMWORD PTR [edi+16], xmm2
	movdqu XMMWORD PTR [edi+176], xmm5
	movdqu XMMWORD PTR [edi+96], xmm6
	movdqu xmm3, XMMWORD PTR [edi+48]
	movdqu xmm4, XMMWORD PTR [edi+64]
	movdqu xmm2, XMMWORD PTR [edi+144]
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 12
	psrld xmm5, 20
	por xmm4, xmm5
	paddd xmm3, xmm4
	pxor xmm1, xmm3
	movdqa xmm5, xmm1
	pslld xmm1, 8
	psrld xmm5, 24
	por xmm1, xmm5
	paddd xmm2, xmm1
	pxor xmm4, xmm2
	movdqa xmm5, xmm4
	pslld xmm4, 7
	psrld xmm5, 25
	por xmm4, xmm5
	movdqu XMMWORD PTR [edi+224], xmm1
	movdqu XMMWORD PTR [edi+144], xmm2
	movdqu xmm0, XMMWORD PTR [edi+32]
	movdqu xmm6, XMMWORD PTR [edi+112]
	movdqu xmm1, XMMWORD PTR [edi+208]
	movdqu xmm5, XMMWORD PTR [edi+128]
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	pshuflw xmm1, xmm1, 177
	pshufhw xmm1, xmm1, 177
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 12
	psrld xmm2, 20
	por xmm6, xmm2
	paddd xmm0, xmm6
	pxor xmm1, xmm0
	movdqa xmm2, xmm1
	pslld xmm1, 8
	psrld xmm2, 24
	por xmm1, xmm2
	paddd xmm5, xmm1
	pxor xmm6, xmm5
	movdqa xmm2, xmm6
	pslld xmm6, 7
	psrld xmm2, 25
	por xmm6, xmm2
	movdqu XMMWORD PTR [edi+32], xmm0
	movdqu XMMWORD PTR [edi+48], xmm3
	movdqu XMMWORD PTR [edi+64], xmm4
	movdqu XMMWORD PTR [edi+112], xmm6
	movdqu XMMWORD PTR [edi+128], xmm5
	movdqu XMMWORD PTR [edi+192], xmm7
	movdqu XMMWORD PTR [edi+208], xmm1
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
	movdqu XMMWORD PTR [edx], xmm6
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
	movdqu XMMWORD PTR [edx+64], xmm6
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
	movdqu XMMWORD PTR [edx+128], xmm6
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
	movdqu XMMWORD PTR [edx+192], xmm6
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
	movdqu XMMWORD PTR [edx+16], xmm6
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
	movdqu XMMWORD PTR [edx+80], xmm6
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
	movdqu XMMWORD PTR [edx+144], xmm6
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
	movdqu XMMWORD PTR [edx+208], xmm6
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
	movdqu XMMWORD PTR [edx+32], xmm6
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
	movdqu XMMWORD PTR [edx+96], xmm6
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
	movdqu XMMWORD PTR [edx+160], xmm6
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
	movdqu XMMWORD PTR [edx+224], xmm6
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
	movdqu XMMWORD PTR [edx+48], xmm6
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
	movdqu XMMWORD PTR [edx+112], xmm6
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
	movdqu XMMWORD PTR [edx+176], xmm6
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
	movdqu XMMWORD PTR [edx+240], xmm6
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
	add edx, 256
	sub ebp, 256
	jmp 268f
267:
	mov ecx, ebp
	and ecx, 15
	and ebp, -16
	add esi, ebp
	add edx, ebp
	mov ebp, edi
	test ecx, ecx
	je 269f
271:
	movzx eax, BYTE PTR [esi]
	xor eax, DWORD PTR [ebp]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	add ebp, 1
	sub ecx, 1
	jne 271b
	jmp 270f
269:
270:
	mov ebp, 0
268:
	cmp ebp, 65
	jae 22b
	jmp 21f
20:
21:
	test ebp, ebp
	je 272f
	mov eax, ebx
	mov ebx, edx
	push edi
	push eax
	call {vg_chacha20_block}
	pop eax
	pop eax
	mov ecx, ebp
	mov ebp, edi
	mov edx, ebx
	cmp ecx, 16
	jb 274f
276:
	movdqu xmm4, XMMWORD PTR [esi]
	movdqu xmm5, XMMWORD PTR [ebp]
	pxor xmm4, xmm5
	movdqu XMMWORD PTR [edx], xmm4
	add esi, 16
	add edx, 16
	add ebp, 16
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
	xor eax, DWORD PTR [ebp]
	mov BYTE PTR [edx], al
	add esi, 1
	add edx, 1
	add ebp, 1
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
