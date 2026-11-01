// The functions of `src/internal/vg_blake2s_compress_avx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
