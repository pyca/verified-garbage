// The functions of `src/blake2s.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_init:
	mov eax, -1150833019
	mov DWORD PTR [rdi+4], eax
	mov eax, 1013904242
	mov DWORD PTR [rdi+8], eax
	mov eax, -1521486534
	mov DWORD PTR [rdi+12], eax
	mov eax, 1359893119
	mov DWORD PTR [rdi+16], eax
	mov eax, -1694144372
	mov DWORD PTR [rdi+20], eax
	mov eax, 528734635
	mov DWORD PTR [rdi+24], eax
	mov eax, 1541459225
	mov DWORD PTR [rdi+28], eax
	mov eax, 1795745383
	mov r8, rcx
	ror r8d, 24
	xor eax, r8d
	xor eax, esi
	mov DWORD PTR [rdi], eax
	test rcx, rcx
	je 20f
	mov eax, 0
	mov QWORD PTR [rdi+32], rax
	mov QWORD PTR [rdi+40], rax
	mov QWORD PTR [rdi+48], rax
	mov QWORD PTR [rdi+56], rax
	mov QWORD PTR [rdi+64], rax
	mov QWORD PTR [rdi+72], rax
	mov QWORD PTR [rdi+80], rax
	mov QWORD PTR [rdi+88], rax
	mov r8d, 0
22:
	movzx eax, BYTE PTR [rdx+r8*1]
	mov BYTE PTR [rdi+r8*1+32], al
	add r8, 1
	sub rcx, 1
	jne 22b
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_blake2s_compress_avx:
	mov r8d, r8d
	movabs rax, 361421592464458498
	vmovq xmm14, rax
	movabs rax, 940142975169071882
	vmovq xmm4, rax
	vpunpcklqdq xmm14, xmm14, xmm4
	movabs rax, 290207319533486593
	vmovq xmm15, rax
	movabs rax, 868928702238099977
	vmovq xmm4, rax
	vpunpcklqdq xmm15, xmm15, xmm4
	movabs rax, -4942790177982912921
	vmovq xmm11, rax
	movabs rax, -6534734903820487822
	vmovq xmm4, rax
	vpunpcklqdq xmm11, xmm11, xmm4
	movabs rax, -7276294671082564993
	vmovq xmm12, rax
	movabs rax, 6620516960021240235
	vmovq xmm4, rax
	vpunpcklqdq xmm12, xmm12, xmm4
	test r8, r8
	je 20f
	mov r8d, -1
	jmp 21f
20:
21:
	test rdx, rdx
	je 22f
24:
	vmovdqu xmm0, XMMWORD PTR [rdi]
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vmovdqa xmm2, xmm11
	vmovq xmm13, rcx
	vmovq xmm4, r8
	vpunpcklqdq xmm13, xmm13, xmm4
	vpxor xmm3, xmm12, xmm13
	vmovdqu xmm6, XMMWORD PTR [rsi]
	vmovdqu xmm7, XMMWORD PTR [rsi+8]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+16]
	vmovdqu xmm9, XMMWORD PTR [rsi+24]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+4]
	vmovdqu xmm7, XMMWORD PTR [rsi+12]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+20]
	vmovdqu xmm9, XMMWORD PTR [rsi+28]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vmovdqu xmm7, XMMWORD PTR [rsi+24]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+40]
	vmovdqu xmm9, XMMWORD PTR [rsi+48]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vpshufd xmm6, xmm6, 255
	vmovdqu xmm7, XMMWORD PTR [rsi+28]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+36]
	vmovdqu xmm9, XMMWORD PTR [rsi+44]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vmovdqu xmm7, XMMWORD PTR [rsi+8]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+28]
	vmovdqu xmm9, XMMWORD PTR [rsi+44]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+40]
	vmovdqu xmm7, XMMWORD PTR [rsi+32]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vpshufd xmm8, xmm8, 255
	vmovdqu xmm9, XMMWORD PTR [rsi+16]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+20]
	vmovdqu xmm7, XMMWORD PTR [rsi+4]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi]
	vmovdqu xmm9, XMMWORD PTR [rsi+44]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+12]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+8]
	vmovdqu xmm9, XMMWORD PTR [rsi+28]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+44]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+12]
	vmovdqu xmm9, XMMWORD PTR [rsi+48]
	vpshufd xmm9, xmm9, 255
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+32]
	vmovdqu xmm7, XMMWORD PTR [rsi]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi]
	vmovdqu xmm9, XMMWORD PTR [rsi+44]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+36]
	vmovdqu xmm7, XMMWORD PTR [rsi+40]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+12]
	vmovdqu xmm9, XMMWORD PTR [rsi+28]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+8]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+24]
	vmovdqu xmm9, XMMWORD PTR [rsi+4]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+28]
	vmovdqu xmm7, XMMWORD PTR [rsi+12]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+44]
	vmovdqu xmm9, XMMWORD PTR [rsi+36]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+36]
	vmovdqu xmm7, XMMWORD PTR [rsi+4]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+40]
	vmovdqu xmm9, XMMWORD PTR [rsi+48]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vpshufd xmm6, xmm6, 255
	vmovdqu xmm7, XMMWORD PTR [rsi]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+20]
	vmovdqu xmm9, XMMWORD PTR [rsi+16]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+32]
	vmovdqu xmm7, XMMWORD PTR [rsi+24]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+40]
	vmovdqu xmm9, XMMWORD PTR [rsi]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+36]
	vmovdqu xmm7, XMMWORD PTR [rsi+20]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+8]
	vmovdqu xmm9, XMMWORD PTR [rsi+40]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi]
	vmovdqu xmm7, XMMWORD PTR [rsi+28]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+8]
	vmovdqu xmm9, XMMWORD PTR [rsi+48]
	vpshufd xmm9, xmm9, 255
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+4]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+44]
	vmovdqu xmm9, XMMWORD PTR [rsi+24]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vpshufd xmm6, xmm6, 85
	vmovdqu xmm7, XMMWORD PTR [rsi+4]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vmovdqu xmm9, XMMWORD PTR [rsi+32]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+8]
	vmovdqu xmm7, XMMWORD PTR [rsi+24]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi]
	vmovdqu xmm9, XMMWORD PTR [rsi+32]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vmovdqu xmm7, XMMWORD PTR [rsi+40]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+44]
	vmovdqu xmm9, XMMWORD PTR [rsi+12]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+4]
	vmovdqu xmm7, XMMWORD PTR [rsi+16]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+20]
	vmovdqu xmm9, XMMWORD PTR [rsi+48]
	vpshufd xmm9, xmm9, 255
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+28]
	vmovdqu xmm7, XMMWORD PTR [rsi+44]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+12]
	vmovdqu xmm9, XMMWORD PTR [rsi+48]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vmovdqu xmm7, XMMWORD PTR [rsi+4]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vmovdqu xmm9, XMMWORD PTR [rsi+8]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+12]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpshufd xmm7, xmm7, 255
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+44]
	vmovdqu xmm9, XMMWORD PTR [rsi+32]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+32]
	vmovdqu xmm7, XMMWORD PTR [rsi]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+24]
	vmovdqu xmm9, XMMWORD PTR [rsi+36]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+44]
	vmovdqu xmm7, XMMWORD PTR [rsi+28]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+12]
	vmovdqu xmm9, XMMWORD PTR [rsi+8]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+44]
	vmovdqu xmm7, XMMWORD PTR [rsi+20]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vmovdqu xmm9, XMMWORD PTR [rsi+12]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+36]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+4]
	vmovdqu xmm9, XMMWORD PTR [rsi+36]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+8]
	vmovdqu xmm7, XMMWORD PTR [rsi+20]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vpshufd xmm8, xmm8, 255
	vmovdqu xmm9, XMMWORD PTR [rsi+24]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+40]
	vmovdqu xmm7, XMMWORD PTR [rsi]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+16]
	vmovdqu xmm9, XMMWORD PTR [rsi+24]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+16]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+44]
	vmovdqu xmm9, XMMWORD PTR [rsi]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+48]
	vpshufd xmm6, xmm6, 255
	vmovdqu xmm7, XMMWORD PTR [rsi+28]
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+12]
	vmovdqu xmm9, XMMWORD PTR [rsi+32]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+40]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vpshufd xmm8, xmm8, 85
	vmovdqu xmm9, XMMWORD PTR [rsi+4]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+20]
	vmovdqu xmm7, XMMWORD PTR [rsi+8]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+28]
	vmovdqu xmm9, XMMWORD PTR [rsi+16]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+40]
	vmovdqu xmm7, XMMWORD PTR [rsi+32]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+28]
	vmovdqu xmm9, XMMWORD PTR [rsi+4]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi+8]
	vmovdqu xmm7, XMMWORD PTR [rsi+16]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+24]
	vmovdqu xmm9, XMMWORD PTR [rsi+20]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 147
	vpshufd xmm2, xmm2, 57
	vpshufd xmm3, xmm3, 78
	vmovdqu xmm6, XMMWORD PTR [rsi+44]
	vmovdqu xmm7, XMMWORD PTR [rsi+48]
	vpshufd xmm7, xmm7, 255
	vpunpckhdq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+36]
	vmovdqu xmm9, XMMWORD PTR [rsi+12]
	vpunpckldq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm14
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 12
	vpslld xmm1, xmm1, 20
	vpor xmm1, xmm1, xmm4
	vmovdqu xmm6, XMMWORD PTR [rsi]
	vmovdqu xmm7, XMMWORD PTR [rsi+44]
	vpunpckldq xmm5, xmm6, xmm7
	vmovdqu xmm8, XMMWORD PTR [rsi+48]
	vmovdqu xmm9, XMMWORD PTR [rsi+40]
	vpunpckhdq xmm8, xmm8, xmm9
	vpunpcklqdq xmm5, xmm5, xmm8
	vpaddd xmm0, xmm0, xmm5
	vpaddd xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm0
	vpshufb xmm3, xmm3, xmm15
	vpaddd xmm2, xmm2, xmm3
	vpxor xmm1, xmm1, xmm2
	vpsrld xmm4, xmm1, 7
	vpslld xmm1, xmm1, 25
	vpor xmm1, xmm1, xmm4
	vpshufd xmm0, xmm0, 57
	vpshufd xmm2, xmm2, 147
	vpshufd xmm3, xmm3, 78
	vpxor xmm0, xmm0, xmm2
	vpxor xmm1, xmm1, xmm3
	vmovdqu xmm4, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm4
	vmovdqu XMMWORD PTR [rdi], xmm0
	vmovdqu xmm4, XMMWORD PTR [rdi+16]
	vpxor xmm1, xmm1, xmm4
	vmovdqu XMMWORD PTR [rdi+16], xmm1
	add rsi, 64
	add rcx, 64
	sub rdx, 1
	jne 24b
	jmp 23f
22:
23:
	ret
	.p2align 6

vg_blake2s_update_avx:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress_avx}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 6
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 64
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress_avx}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 63
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2s_finalize_avx:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 64
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2s_compress_avx}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2s_compress:
	mov QWORD PTR [r9+296], rbx
	mov QWORD PTR [r9+304], rbp
	mov QWORD PTR [r9+312], r12
	mov QWORD PTR [r9+320], r13
	mov QWORD PTR [r9+328], r14
	mov QWORD PTR [r9+336], r15
	mov r8d, r8d
	mov QWORD PTR [r9+256], rsi
	mov QWORD PTR [r9+264], rdx
	mov QWORD PTR [r9+272], rcx
	mov eax, 0
	mov QWORD PTR [r9+280], rax
	test r8, r8
	je 20f
	mov rax, -1
	jmp 21f
20:
21:
	mov QWORD PTR [r9+288], rax
	test rdx, rdx
	je 22f
24:
	mov rsi, QWORD PTR [r9+256]
	mov eax, DWORD PTR [rsi]
	mov DWORD PTR [r9], eax
	mov eax, DWORD PTR [rsi+4]
	mov DWORD PTR [r9+4], eax
	mov eax, DWORD PTR [rsi+8]
	mov DWORD PTR [r9+8], eax
	mov eax, DWORD PTR [rsi+12]
	mov DWORD PTR [r9+12], eax
	mov eax, DWORD PTR [rsi+16]
	mov DWORD PTR [r9+16], eax
	mov eax, DWORD PTR [rsi+20]
	mov DWORD PTR [r9+20], eax
	mov eax, DWORD PTR [rsi+24]
	mov DWORD PTR [r9+24], eax
	mov eax, DWORD PTR [rsi+28]
	mov DWORD PTR [r9+28], eax
	mov eax, DWORD PTR [rsi+32]
	mov DWORD PTR [r9+32], eax
	mov eax, DWORD PTR [rsi+36]
	mov DWORD PTR [r9+36], eax
	mov eax, DWORD PTR [rsi+40]
	mov DWORD PTR [r9+40], eax
	mov eax, DWORD PTR [rsi+44]
	mov DWORD PTR [r9+44], eax
	mov eax, DWORD PTR [rsi+48]
	mov DWORD PTR [r9+48], eax
	mov eax, DWORD PTR [rsi+52]
	mov DWORD PTR [r9+52], eax
	mov eax, DWORD PTR [rsi+56]
	mov DWORD PTR [r9+56], eax
	mov eax, DWORD PTR [rsi+60]
	mov DWORD PTR [r9+60], eax
	mov eax, 1779033703
	mov DWORD PTR [r9+192], eax
	mov eax, 1013904242
	mov DWORD PTR [r9+208], eax
	mov eax, -1521486534
	mov DWORD PTR [r9+216], eax
	mov eax, DWORD PTR [rdi]
	mov ebx, DWORD PTR [rdi+4]
	mov ecx, DWORD PTR [rdi+8]
	mov edx, DWORD PTR [rdi+12]
	mov esi, DWORD PTR [rdi+16]
	mov r15d, DWORD PTR [rdi+20]
	mov ebp, DWORD PTR [rdi+24]
	mov r8d, DWORD PTR [rdi+28]
	mov r14d, -1150833019
	mov r10d, 1359893119
	xor r10d, DWORD PTR [r9+272]
	mov r11d, -1694144372
	xor r11d, DWORD PTR [r9+276]
	mov r12d, 528734635
	xor r12d, DWORD PTR [r9+288]
	mov r13d, 1541459225
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+4]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+8]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+12]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+16]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+20]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+24]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+28]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+32]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+36]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+40]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+44]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+48]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+52]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+56]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+60]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+56]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+40]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+16]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+32]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+36]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+60]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+52]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+24]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+4]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+48]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+8]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+44]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+28]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+20]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+12]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+44]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+32]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+48]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+20]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+8]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+60]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+52]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+40]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+56]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+12]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+24]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+28]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+4]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+36]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+16]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+28]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+36]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+12]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+4]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+52]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+48]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+44]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+56]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+8]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+24]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+20]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+40]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+16]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+60]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+32]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+36]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+20]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+28]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+8]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+16]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+40]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+60]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+56]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+4]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+44]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+48]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+24]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+32]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+12]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+52]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+8]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+48]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+24]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+40]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+44]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+32]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+12]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+16]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+52]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+28]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+20]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+60]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+56]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+4]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+36]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+48]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+20]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+4]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+60]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+56]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+52]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+16]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+40]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+28]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+24]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+12]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+36]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+8]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+32]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+44]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+52]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+44]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+28]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+56]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+48]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+4]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+12]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+36]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+20]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+60]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+16]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+32]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+24]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+8]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+40]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+24]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+60]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+56]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+36]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+44]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+12]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+32]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+48]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+8]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+52]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+28]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+4]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+16]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+40]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9+20]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+192]
	add eax, esi
	add eax, DWORD PTR [r9+40]
	xor r10d, eax
	ror r10d, 16
	add r14d, r10d
	xor esi, r14d
	ror esi, 12
	add eax, esi
	add eax, DWORD PTR [r9+8]
	xor r10d, eax
	ror r10d, 8
	add r14d, r10d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add ebx, r15d
	add ebx, DWORD PTR [r9+32]
	xor r11d, ebx
	ror r11d, 16
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 12
	add ebx, r15d
	add ebx, DWORD PTR [r9+16]
	xor r11d, ebx
	ror r11d, 8
	add r14d, r11d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+200], r14d
	mov r14d, DWORD PTR [r9+208]
	add ecx, ebp
	add ecx, DWORD PTR [r9+28]
	xor r12d, ecx
	ror r12d, 16
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 12
	add ecx, ebp
	add ecx, DWORD PTR [r9+24]
	xor r12d, ecx
	ror r12d, 8
	add r14d, r12d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add edx, r8d
	add edx, DWORD PTR [r9+4]
	xor r13d, edx
	ror r13d, 16
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 12
	add edx, r8d
	add edx, DWORD PTR [r9+20]
	xor r13d, edx
	ror r13d, 8
	add r14d, r13d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+208]
	add eax, r15d
	add eax, DWORD PTR [r9+60]
	xor r13d, eax
	ror r13d, 16
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 12
	add eax, r15d
	add eax, DWORD PTR [r9+44]
	xor r13d, eax
	ror r13d, 8
	add r14d, r13d
	xor r15d, r14d
	ror r15d, 7
	mov DWORD PTR [r9+208], r14d
	mov r14d, DWORD PTR [r9+216]
	add ebx, ebp
	add ebx, DWORD PTR [r9+36]
	xor r10d, ebx
	ror r10d, 16
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 12
	add ebx, ebp
	add ebx, DWORD PTR [r9+56]
	xor r10d, ebx
	ror r10d, 8
	add r14d, r10d
	xor ebp, r14d
	ror ebp, 7
	mov DWORD PTR [r9+216], r14d
	mov r14d, DWORD PTR [r9+192]
	add ecx, r8d
	add ecx, DWORD PTR [r9+12]
	xor r11d, ecx
	ror r11d, 16
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 12
	add ecx, r8d
	add ecx, DWORD PTR [r9+48]
	xor r11d, ecx
	ror r11d, 8
	add r14d, r11d
	xor r8d, r14d
	ror r8d, 7
	mov DWORD PTR [r9+192], r14d
	mov r14d, DWORD PTR [r9+200]
	add edx, esi
	add edx, DWORD PTR [r9+52]
	xor r12d, edx
	ror r12d, 16
	add r14d, r12d
	xor esi, r14d
	ror esi, 12
	add edx, esi
	add edx, DWORD PTR [r9]
	xor r12d, edx
	ror r12d, 8
	add r14d, r12d
	xor esi, r14d
	ror esi, 7
	mov DWORD PTR [r9+200], r14d
	mov DWORD PTR [r9+224], r10d
	mov DWORD PTR [r9+232], r11d
	mov DWORD PTR [r9+240], r12d
	mov DWORD PTR [r9+248], r13d
	xor eax, DWORD PTR [r9+192]
	xor eax, DWORD PTR [rdi]
	mov DWORD PTR [rdi], eax
	xor ebx, DWORD PTR [r9+200]
	xor ebx, DWORD PTR [rdi+4]
	mov DWORD PTR [rdi+4], ebx
	xor ecx, DWORD PTR [r9+208]
	xor ecx, DWORD PTR [rdi+8]
	mov DWORD PTR [rdi+8], ecx
	xor edx, DWORD PTR [r9+216]
	xor edx, DWORD PTR [rdi+12]
	mov DWORD PTR [rdi+12], edx
	xor esi, DWORD PTR [r9+224]
	xor esi, DWORD PTR [rdi+16]
	mov DWORD PTR [rdi+16], esi
	xor r15d, DWORD PTR [r9+232]
	xor r15d, DWORD PTR [rdi+20]
	mov DWORD PTR [rdi+20], r15d
	xor ebp, DWORD PTR [r9+240]
	xor ebp, DWORD PTR [rdi+24]
	mov DWORD PTR [rdi+24], ebp
	xor r8d, DWORD PTR [r9+248]
	xor r8d, DWORD PTR [rdi+28]
	mov DWORD PTR [rdi+28], r8d
	mov rsi, QWORD PTR [r9+256]
	add rsi, 64
	mov QWORD PTR [r9+256], rsi
	mov rcx, QWORD PTR [r9+272]
	add rcx, 64
	mov QWORD PTR [r9+272], rcx
	mov rdx, QWORD PTR [r9+264]
	sub rdx, 1
	mov QWORD PTR [r9+264], rdx
	jne 24b
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r9+296]
	mov rbp, QWORD PTR [r9+304]
	mov r12, QWORD PTR [r9+312]
	mov r13, QWORD PTR [r9+320]
	mov r14, QWORD PTR [r9+328]
	mov r15, QWORD PTR [r9+336]
	ret
	.p2align 6

vg_blake2s_update:
	lea rsp, [rsp-584]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+512], rbx
	mov QWORD PTR [r8+520], rbp
	mov QWORD PTR [r8+528], r12
	mov QWORD PTR [r8+536], r13
	mov QWORD PTR [r8+544], r14
	mov QWORD PTR [r8+552], r15
	mov rbx, rdi
	mov r15, r8
	mov rbp, rdx
	mov r12, rcx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	test r12, r12
	je 22f
	test r13, r13
	je 24f
	mov eax, 64
	sub rax, r13
	cmp r12, rax
	jb 26f
	jmp 27f
26:
	mov rax, r12
27:
	sub r12, rax
	add r14, rax
	test rax, rax
	je 28f
210:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 210b
	jmp 29f
28:
29:
	test r12, r12
	je 211f
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress}
	mov rbx, rdi
	mov r15, r9
	mov r13d, 0
	jmp 212f
211:
212:
	jmp 25f
24:
25:
	test r12, r12
	je 213f
	mov rax, r12
	sub rax, 1
	shr rax, 6
	test rax, rax
	je 215f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, rax
	mov rcx, r14
	add rcx, 64
	mov r8d, 0
	mov r9, r15
	call {vg_blake2s_compress}
	mov rbx, rdi
	mov r15, r9
	mov rax, r12
	sub rax, 1
	and rax, 63
	add rax, 1
	sub r12, rax
	add rbp, r12
	add r14, r12
	mov r12, rax
	jmp 216f
215:
216:
	mov rax, r12
	add r14, rax
	mov r12d, 0
217:
	movzx r9d, BYTE PTR [rbp]
	mov BYTE PTR [rbx+r13*1+32], r9b
	add rbp, 1
	add r13, 1
	sub rax, 1
	jne 217b
	jmp 214f
213:
214:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6

vg_blake2s_finalize:
	lea rsp, [rsp-584]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+512], rbx
	mov QWORD PTR [rcx+520], rbp
	mov QWORD PTR [rcx+528], r12
	mov QWORD PTR [rcx+536], r13
	mov QWORD PTR [rcx+544], r14
	mov QWORD PTR [rcx+552], r15
	mov rbx, rdi
	mov r15, rcx
	mov rbp, rdx
	mov r14, rsi
	mov r13, r14
	sub r13, 1
	and r13, 63
	add r13, 1
	test r14, r14
	je 20f
	jmp 21f
20:
	mov r13d, 0
21:
	mov r9d, 0
	mov eax, 64
	sub rax, r13
	je 22f
24:
	mov BYTE PTR [rbx+r13*1+32], r9b
	add r13, 1
	sub rax, 1
	jne 24b
	jmp 23f
22:
23:
	mov rdi, rbx
	mov rsi, rbx
	add rsi, 32
	mov edx, 1
	mov rcx, r14
	mov r8d, 1
	mov r9, r15
	call {vg_blake2s_compress}
	mov rbx, rdi
	mov r15, r9
	mov rax, QWORD PTR [rbx]
	mov QWORD PTR [rbp], rax
	mov rax, QWORD PTR [rbx+8]
	mov QWORD PTR [rbp+8], rax
	mov rax, QWORD PTR [rbx+16]
	mov QWORD PTR [rbp+16], rax
	mov rax, QWORD PTR [rbx+24]
	mov QWORD PTR [rbp+24], rax
	mov rbx, QWORD PTR [r15+512]
	mov rbp, QWORD PTR [r15+520]
	mov r12, QWORD PTR [r15+528]
	mov r13, QWORD PTR [r15+536]
	mov r14, QWORD PTR [r15+544]
	mov r15, QWORD PTR [r15+552]
	lea rsp, [rsp+584]
	ret
	.p2align 6
