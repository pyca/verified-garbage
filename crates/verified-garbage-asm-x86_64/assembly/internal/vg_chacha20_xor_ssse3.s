// The functions of `src/internal/vg_chacha20_xor_ssse3.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_ssse3:
	movabs rax, 361421592464458498
	mov QWORD PTR [rcx+272], rax
	movabs rax, 940142975169071882
	mov QWORD PTR [rcx+280], rax
	movabs rax, 433757367256023043
	mov QWORD PTR [rcx+288], rax
	movabs rax, 1012478749960636427
	mov QWORD PTR [rcx+296], rax
	cmp rdx, 65
	jb 20f
22:
	movdqu xmm4, XMMWORD PTR [rdi]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [rcx], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [rcx+16], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [rcx+32], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [rcx+48], xmm0
	movdqu xmm4, XMMWORD PTR [rdi+16]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [rcx+64], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [rcx+80], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [rcx+96], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [rcx+112], xmm0
	movdqu xmm4, XMMWORD PTR [rdi+32]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [rcx+128], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [rcx+144], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [rcx+160], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [rcx+176], xmm0
	movdqu xmm4, XMMWORD PTR [rdi+48]
	pshufd xmm0, xmm4, 0
	movdqu XMMWORD PTR [rcx+192], xmm0
	pshufd xmm0, xmm4, 85
	movdqu XMMWORD PTR [rcx+208], xmm0
	pshufd xmm0, xmm4, 170
	movdqu XMMWORD PTR [rcx+224], xmm0
	pshufd xmm0, xmm4, 255
	movdqu XMMWORD PTR [rcx+240], xmm0
	mov eax, DWORD PTR [rdi+48]
	mov DWORD PTR [rcx+192], eax
	mov DWORD PTR [rcx+256], eax
	add eax, 1
	mov DWORD PTR [rcx+196], eax
	mov DWORD PTR [rcx+260], eax
	add eax, 1
	mov DWORD PTR [rcx+200], eax
	mov DWORD PTR [rcx+264], eax
	add eax, 1
	mov DWORD PTR [rcx+204], eax
	mov DWORD PTR [rcx+268], eax
	add eax, 1
	movdqu xmm0, XMMWORD PTR [rcx]
	movdqu xmm1, XMMWORD PTR [rcx+16]
	movdqu xmm2, XMMWORD PTR [rcx+32]
	movdqu xmm3, XMMWORD PTR [rcx+48]
	movdqu xmm4, XMMWORD PTR [rcx+64]
	movdqu xmm5, XMMWORD PTR [rcx+80]
	movdqu xmm6, XMMWORD PTR [rcx+96]
	movdqu xmm7, XMMWORD PTR [rcx+112]
	movdqu xmm8, XMMWORD PTR [rcx+128]
	movdqu xmm9, XMMWORD PTR [rcx+144]
	movdqu xmm10, XMMWORD PTR [rcx+160]
	movdqu xmm11, XMMWORD PTR [rcx+176]
	movdqu xmm12, XMMWORD PTR [rcx+192]
	movdqu xmm13, XMMWORD PTR [rcx+208]
	movdqu xmm14, XMMWORD PTR [rcx+224]
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm0, xmm4
	pxor xmm12, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm8, xmm12
	pxor xmm4, xmm8
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm1, xmm5
	pxor xmm13, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm9, xmm13
	pxor xmm5, xmm9
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm2, xmm6
	pxor xmm14, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm10, xmm14
	pxor xmm6, xmm10
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+240]
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm3, xmm7
	pxor xmm4, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm11, xmm4
	pxor xmm7, xmm11
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 12
	psrld xmm15, 20
	por xmm5, xmm15
	paddd xmm0, xmm5
	pxor xmm4, xmm0
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm4, xmm15
	paddd xmm10, xmm4
	pxor xmm5, xmm10
	movdqa xmm15, xmm5
	pslld xmm5, 7
	psrld xmm15, 25
	por xmm5, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 12
	psrld xmm15, 20
	por xmm6, xmm15
	paddd xmm1, xmm6
	pxor xmm12, xmm1
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm12, xmm15
	paddd xmm11, xmm12
	pxor xmm6, xmm11
	movdqa xmm15, xmm6
	pslld xmm6, 7
	psrld xmm15, 25
	por xmm6, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 12
	psrld xmm15, 20
	por xmm7, xmm15
	paddd xmm2, xmm7
	pxor xmm13, xmm2
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm13, xmm15
	paddd xmm8, xmm13
	pxor xmm7, xmm8
	movdqa xmm15, xmm7
	pslld xmm7, 7
	psrld xmm15, 25
	por xmm7, xmm15
	movdqu XMMWORD PTR [rcx+240], xmm4
	movdqu xmm4, XMMWORD PTR [rcx+64]
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+272]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 12
	psrld xmm15, 20
	por xmm4, xmm15
	paddd xmm3, xmm4
	pxor xmm14, xmm3
	movdqu xmm15, XMMWORD PTR [rcx+288]
	pshufb xmm14, xmm15
	paddd xmm9, xmm14
	pxor xmm4, xmm9
	movdqa xmm15, xmm4
	pslld xmm4, 7
	psrld xmm15, 25
	por xmm4, xmm15
	movdqu XMMWORD PTR [rcx], xmm0
	movdqu XMMWORD PTR [rcx+16], xmm1
	movdqu XMMWORD PTR [rcx+32], xmm2
	movdqu XMMWORD PTR [rcx+48], xmm3
	movdqu XMMWORD PTR [rcx+64], xmm4
	movdqu XMMWORD PTR [rcx+80], xmm5
	movdqu XMMWORD PTR [rcx+96], xmm6
	movdqu XMMWORD PTR [rcx+112], xmm7
	movdqu XMMWORD PTR [rcx+128], xmm8
	movdqu XMMWORD PTR [rcx+144], xmm9
	movdqu XMMWORD PTR [rcx+160], xmm10
	movdqu XMMWORD PTR [rcx+176], xmm11
	movdqu XMMWORD PTR [rcx+192], xmm12
	movdqu XMMWORD PTR [rcx+208], xmm13
	movdqu XMMWORD PTR [rcx+224], xmm14
	movdqu xmm0, XMMWORD PTR [rcx]
	movdqu xmm1, XMMWORD PTR [rcx+16]
	movdqu xmm2, XMMWORD PTR [rcx+32]
	movdqu xmm3, XMMWORD PTR [rcx+48]
	movdqu xmm4, XMMWORD PTR [rdi]
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
	cmp rdx, 16
	jb 23f
	movdqu xmm6, XMMWORD PTR [rsi]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [rsi], xmm6
	jmp 24f
23:
	cmp rdx, 1
	jb 25f
	movdqu XMMWORD PTR [rcx], xmm1
	jmp 26f
25:
26:
24:
	cmp rdx, 80
	jb 27f
	movdqu xmm6, XMMWORD PTR [rsi+64]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [rsi+64], xmm6
	jmp 28f
27:
	cmp rdx, 65
	jb 29f
	movdqu XMMWORD PTR [rcx], xmm4
	jmp 210f
29:
210:
28:
	cmp rdx, 144
	jb 211f
	movdqu xmm6, XMMWORD PTR [rsi+128]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [rsi+128], xmm6
	jmp 212f
211:
	cmp rdx, 129
	jb 213f
	movdqu XMMWORD PTR [rcx], xmm3
	jmp 214f
213:
214:
212:
	cmp rdx, 208
	jb 215f
	movdqu xmm6, XMMWORD PTR [rsi+192]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rsi+192], xmm6
	jmp 216f
215:
	cmp rdx, 193
	jb 217f
	movdqu XMMWORD PTR [rcx], xmm0
	jmp 218f
217:
218:
216:
	movdqu xmm0, XMMWORD PTR [rcx+64]
	movdqu xmm1, XMMWORD PTR [rcx+80]
	movdqu xmm2, XMMWORD PTR [rcx+96]
	movdqu xmm3, XMMWORD PTR [rcx+112]
	movdqu xmm4, XMMWORD PTR [rdi+16]
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
	cmp rdx, 32
	jb 219f
	movdqu xmm6, XMMWORD PTR [rsi+16]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [rsi+16], xmm6
	jmp 220f
219:
	cmp rdx, 17
	jb 221f
	movdqu XMMWORD PTR [rcx], xmm1
	jmp 222f
221:
222:
220:
	cmp rdx, 96
	jb 223f
	movdqu xmm6, XMMWORD PTR [rsi+80]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [rsi+80], xmm6
	jmp 224f
223:
	cmp rdx, 81
	jb 225f
	movdqu XMMWORD PTR [rcx], xmm4
	jmp 226f
225:
226:
224:
	cmp rdx, 160
	jb 227f
	movdqu xmm6, XMMWORD PTR [rsi+144]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [rsi+144], xmm6
	jmp 228f
227:
	cmp rdx, 145
	jb 229f
	movdqu XMMWORD PTR [rcx], xmm3
	jmp 230f
229:
230:
228:
	cmp rdx, 224
	jb 231f
	movdqu xmm6, XMMWORD PTR [rsi+208]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rsi+208], xmm6
	jmp 232f
231:
	cmp rdx, 209
	jb 233f
	movdqu XMMWORD PTR [rcx], xmm0
	jmp 234f
233:
234:
232:
	movdqu xmm0, XMMWORD PTR [rcx+128]
	movdqu xmm1, XMMWORD PTR [rcx+144]
	movdqu xmm2, XMMWORD PTR [rcx+160]
	movdqu xmm3, XMMWORD PTR [rcx+176]
	movdqu xmm4, XMMWORD PTR [rdi+32]
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
	cmp rdx, 48
	jb 235f
	movdqu xmm6, XMMWORD PTR [rsi+32]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [rsi+32], xmm6
	jmp 236f
235:
	cmp rdx, 33
	jb 237f
	movdqu XMMWORD PTR [rcx], xmm1
	jmp 238f
237:
238:
236:
	cmp rdx, 112
	jb 239f
	movdqu xmm6, XMMWORD PTR [rsi+96]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [rsi+96], xmm6
	jmp 240f
239:
	cmp rdx, 97
	jb 241f
	movdqu XMMWORD PTR [rcx], xmm4
	jmp 242f
241:
242:
240:
	cmp rdx, 176
	jb 243f
	movdqu xmm6, XMMWORD PTR [rsi+160]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [rsi+160], xmm6
	jmp 244f
243:
	cmp rdx, 161
	jb 245f
	movdqu XMMWORD PTR [rcx], xmm3
	jmp 246f
245:
246:
244:
	cmp rdx, 240
	jb 247f
	movdqu xmm6, XMMWORD PTR [rsi+224]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rsi+224], xmm6
	jmp 248f
247:
	cmp rdx, 225
	jb 249f
	movdqu XMMWORD PTR [rcx], xmm0
	jmp 250f
249:
250:
248:
	movdqu xmm0, XMMWORD PTR [rcx+192]
	movdqu xmm1, XMMWORD PTR [rcx+208]
	movdqu xmm2, XMMWORD PTR [rcx+224]
	movdqu xmm3, XMMWORD PTR [rcx+240]
	movdqu xmm4, XMMWORD PTR [rdi+48]
	movdqu xmm5, XMMWORD PTR [rcx+256]
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
	cmp rdx, 64
	jb 251f
	movdqu xmm6, XMMWORD PTR [rsi+48]
	pxor xmm6, xmm1
	movdqu XMMWORD PTR [rsi+48], xmm6
	jmp 252f
251:
	cmp rdx, 49
	jb 253f
	movdqu XMMWORD PTR [rcx], xmm1
	jmp 254f
253:
254:
252:
	cmp rdx, 128
	jb 255f
	movdqu xmm6, XMMWORD PTR [rsi+112]
	pxor xmm6, xmm4
	movdqu XMMWORD PTR [rsi+112], xmm6
	jmp 256f
255:
	cmp rdx, 113
	jb 257f
	movdqu XMMWORD PTR [rcx], xmm4
	jmp 258f
257:
258:
256:
	cmp rdx, 192
	jb 259f
	movdqu xmm6, XMMWORD PTR [rsi+176]
	pxor xmm6, xmm3
	movdqu XMMWORD PTR [rsi+176], xmm6
	jmp 260f
259:
	cmp rdx, 177
	jb 261f
	movdqu XMMWORD PTR [rcx], xmm3
	jmp 262f
261:
262:
260:
	cmp rdx, 256
	jb 263f
	movdqu xmm6, XMMWORD PTR [rsi+240]
	pxor xmm6, xmm0
	movdqu XMMWORD PTR [rsi+240], xmm6
	jmp 264f
263:
	cmp rdx, 241
	jb 265f
	movdqu XMMWORD PTR [rcx], xmm0
	jmp 266f
265:
266:
264:
	cmp rdx, 257
	jb 267f
	mov eax, DWORD PTR [rdi+48]
	add eax, 4
	mov DWORD PTR [rdi+48], eax
	add rsi, 256
	sub rdx, 256
	jmp 268f
267:
	mov r9, rcx
	mov rax, rdx
	and rax, -16
	add rsi, rax
	and rdx, 15
	mov ecx, 0
	mov rax, rdx
	shr rax, 3
	je 269f
271:
	mov r8, QWORD PTR [rsi+rcx*1]
	xor r8, QWORD PTR [r9+rcx*1]
	mov QWORD PTR [rsi+rcx*1], r8
	add rcx, 8
	sub rax, 1
	jne 271b
	jmp 270f
269:
270:
	cmp rcx, rdx
	je 272f
274:
	movzx eax, BYTE PTR [rsi+rcx*1]
	movzx r8d, BYTE PTR [r9+rcx*1]
	xor rax, r8
	mov BYTE PTR [rsi+rcx*1], al
	add rcx, 1
	cmp rcx, rdx
	jne 274b
	jmp 273f
272:
273:
	mov rcx, r9
	add rsi, rdx
	mov edx, 0
268:
	cmp rdx, 65
	jae 22b
	jmp 21f
20:
21:
	test rdx, rdx
	je 275f
	call {vg_chacha20_xor}
	jmp 276f
275:
	mov rsi, rcx
276:
	ret
	.p2align 6
