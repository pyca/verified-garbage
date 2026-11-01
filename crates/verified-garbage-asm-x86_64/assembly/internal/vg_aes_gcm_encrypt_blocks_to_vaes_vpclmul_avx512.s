// The functions of `src/internal/vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_encrypt_blocks_to_vaes_vpclmul_avx512:
	mov r11, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+8]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
	mov QWORD PTR [r11+48], r10
	cmp r9, 16
	jb 20f
	mov rax, r9
	and rax, 15
	sub r9, rax
	add r11, 64
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [rdi+240]
	pshufb xmm7, xmm0
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm13, XMMWORD PTR [rax+32]
	movabs rax, -1
	movq xmm14, rax
	punpcklqdq xmm14, xmm14
	movdqa xmm3, xmm7
	psllq xmm3, 1
	movdqa xmm11, xmm7
	psrlq xmm11, 63
	pslldq xmm11, 8
	por xmm3, xmm11
	pshufd xmm11, xmm7, 255
	psrld xmm11, 31
	paddd xmm11, xmm14
	pandn xmm11, xmm13
	pxor xmm3, xmm11
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm3
	pclmulqdq xmm11, xmm3, 16
	pxor xmm9, xmm11
	movdqa xmm11, xmm9
	psrldq xmm11, 8
	pxor xmm10, xmm11
	pslldq xmm9, 8
	pxor xmm8, xmm9
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm11, xmm8
	pclmulqdq xmm11, xmm1, 16
	pshufd xmm8, xmm8, 78
	pxor xmm8, xmm11
	movdqa xmm4, xmm10
	pxor xmm4, xmm8
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqa xmm2, xmm2
	vinserti128 ymm12, ymm4, xmm3, 1
	vinserti128 ymm7, ymm4, xmm4, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm13, ymm10, ymm8
	vinserti128 ymm7, ymm13, xmm13, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm14, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm13, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm15, ymm10, ymm8
	vinserti128 ymm7, ymm15, xmm15, 1
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm15, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm15, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm3, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm14, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm14, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm4, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm13, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm5, ymm10, ymm8
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpclmulqdq ymm11, ymm12, ymm7, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpsrldq ymm11, ymm9, 8
	vpxor ymm10, ymm10, ymm11
	vpslldq ymm9, ymm9, 8
	vpxor ymm8, ymm8, ymm9
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm6, ymm10, ymm8
	vmovdqu YMMWORD PTR [r11], ymm3
	vmovdqu YMMWORD PTR [r11+32], ymm4
	vmovdqu YMMWORD PTR [r11+64], ymm5
	vmovdqu YMMWORD PTR [r11+96], ymm6
	vmovdqu YMMWORD PTR [r11+128], ymm15
	vmovdqu YMMWORD PTR [r11+160], ymm14
	vmovdqu YMMWORD PTR [r11+192], ymm13
	vmovdqu YMMWORD PTR [r11+224], ymm12
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	movabs rax, 1
	vmovq xmm15, rax
	vmovdqu xmm14, XMMWORD PTR [rdx]
	vpshufb xmm14, xmm14, xmm0
	vpaddd xmm13, xmm14, xmm15
	vinserti128 ymm14, ymm14, xmm13, 1
	movabs rax, 2
	vmovq xmm15, rax
	vinserti128 ymm15, ymm15, xmm15, 1
	sub r8, r10
	mov rax, rdx
	mov rdx, r10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vshufi32x4 zmm1, zmm1, zmm1, 68
	vmovdqa xmm2, xmm2
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 22f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 24f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+64]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+64], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+128]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+128], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+192]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+192], zmm6
	cmp r9, 256
	jb 26f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [r11]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+256], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+320], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+128]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+384], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+192]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+448], zmm10
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+256]
	vmovdqu32 zmm7, ZMMWORD PTR [r11]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+512], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+64]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+576], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+128]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+640], zmm10
	vmovdqu32 zmm7, ZMMWORD PTR [r11+192]
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vmovdqu32 ZMMWORD PTR [r11+704], zmm10
	vmovdqu32 ZMMWORD PTR [r11+832], zmm1
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 28f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 210f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 211f
210:
211:
	jmp 29f
28:
29:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 212f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 214f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+512]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+512], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+576]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+576], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+640]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+640], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+704]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+704], zmm6
216:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+512]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+576]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpxord zmm8, zmm11, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpxord zmm10, zmm11, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpxord zmm9, zmm11, zmm2
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+640]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+704]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 217f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 219f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 220f
219:
220:
	jmp 218f
217:
218:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+768]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+768], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+832]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+832], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+896]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+896], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+960]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+960], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+256]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+256]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+320]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+320]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+384]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+384]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+448]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+448]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 221f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 223f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 224f
223:
224:
	jmp 222f
221:
222:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1024]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1024], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1088]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1088], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1152]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1152], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1216]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1216], zmm6
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+512]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+576]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+640]
	vmovdqu32 zmm13, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm1, ZMMWORD PTR [rdx+704]
	vpshufb zmm7, zmm7, zmm0
	vpshufb zmm1, zmm1, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpclmulqdq zmm2, zmm1, zmm13, 0
	vpternlogd zmm8, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpclmulqdq zmm2, zmm1, zmm13, 17
	vpternlogd zmm10, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm2, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vpclmulqdq zmm11, zmm1, zmm13, 1
	vpclmulqdq zmm2, zmm1, zmm13, 16
	vpternlogd zmm9, zmm11, zmm2, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 225f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 227f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 228f
227:
228:
	jmp 226f
225:
226:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1280]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1280], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1344]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1344], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1408]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1408], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+1472]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+1472], zmm6
	add rdx, 768
	sub r9, 48
	cmp r9, 96
	jae 216b
	vmovdqu32 zmm1, ZMMWORD PTR [r11+832]
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	add rdx, 256
	sub r9, 16
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	add rdx, 256
	sub r9, 16
	jmp 27f
26:
27:
	cmp r9, 32
	jb 229f
231:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm4, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm5, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vpshufb zmm6, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vpxord zmm4, zmm4, zmm13
	vpxord zmm5, zmm5, zmm13
	vpxord zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 10
	je 232f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	cmp rsi, 12
	je 234f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	vaesenc zmm4, zmm4, zmm13
	vaesenc zmm5, zmm5, zmm13
	vaesenc zmm6, zmm6, zmm13
	jmp 235f
234:
235:
	jmp 233f
232:
233:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vaesenclast zmm4, zmm4, zmm13
	vaesenclast zmm5, zmm5, zmm13
	vaesenclast zmm6, zmm6, zmm13
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+256]
	vpxord zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+256], zmm3
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+320]
	vpxord zmm4, zmm4, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+320], zmm4
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+384]
	vpxord zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+384], zmm5
	vmovdqu32 zmm13, ZMMWORD PTR [rdx+r8*1+448]
	vpxord zmm6, zmm6, zmm13
	vmovdqu32 ZMMWORD PTR [rdx+448], zmm6
	add rdx, 256
	sub r9, 16
	cmp r9, 32
	jae 231b
	jmp 230f
229:
230:
	vpshufb xmm13, xmm14, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	vmovdqu32 zmm12, ZMMWORD PTR [r11+64]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+64]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm8, zmm7, zmm12, 0
	vpclmulqdq zmm10, zmm7, zmm12, 17
	vpclmulqdq zmm9, zmm7, zmm12, 1
	vpclmulqdq zmm11, zmm7, zmm12, 16
	vpxord zmm9, zmm9, zmm11
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11+192]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+192]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vmovdqu32 zmm12, ZMMWORD PTR [r11]
	vmovdqu32 zmm7, ZMMWORD PTR [rdx]
	vpshufb zmm7, zmm7, zmm0
	vpxord zmm7, zmm7, zmm2
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	vpclmulqdq zmm11, zmm8, zmm1, 16
	vpshufd zmm8, zmm8, 78
	vpternlogd zmm9, zmm8, zmm11, 150
	vpclmulqdq zmm11, zmm9, zmm1, 16
	vpshufd zmm9, zmm9, 78
	vpternlogd zmm10, zmm9, zmm11, 150
	vshufi32x4 zmm11, zmm10, zmm10, 14
	vpxor ymm10, ymm10, ymm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm2, xmm10, xmm11
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	jmp 21f
20:
21:
	mov r11, QWORD PTR [rsp+24]
	mov r8, QWORD PTR [r11+40]
	mov rax, r8
	and r8, 15
	sub rax, r8
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	mov rcx, rax
	add rax, QWORD PTR [r11+32]
	mov QWORD PTR [r11+32], rax
	add rcx, QWORD PTR [r11+48]
	mov QWORD PTR [r11+48], rcx
	mov QWORD PTR [r11+40], r8
	mov r11, QWORD PTR [rsp+24]
	mov rcx, QWORD PTR [r11+40]
	test rcx, rcx
	je 236f
	mov rsi, QWORD PTR [r11+32]
	mov rdi, QWORD PTR [r11+48]
	mov r10d, 0
238:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	sub rcx, 1
	jne 238b
	mov r11, QWORD PTR [rsp+24]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+48]
	mov r9, QWORD PTR [r11+40]
	mov rax, r11
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512}
	pop rax
	jmp 237f
236:
237:
	ret
	.p2align 6
