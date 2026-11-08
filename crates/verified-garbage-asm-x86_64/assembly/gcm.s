// The functions of `src/gcm.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_prepare_vpclmul_avx512:
	mov rax, 48
	mov QWORD PTR [rdi+1024], rax
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
	vmovdqu YMMWORD PTR [rdi+256], ymm12
	vmovdqu YMMWORD PTR [rdi+288], ymm13
	vmovdqu YMMWORD PTR [rdi+320], ymm14
	vmovdqu YMMWORD PTR [rdi+352], ymm15
	vmovdqu YMMWORD PTR [rdi+384], ymm6
	vmovdqu YMMWORD PTR [rdi+416], ymm5
	vmovdqu YMMWORD PTR [rdi+448], ymm4
	vmovdqu YMMWORD PTR [rdi+480], ymm3
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
	mov r11, rdi
	add r11, 256
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+224]
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
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+480]
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
	vzeroupper
	ret
	.p2align 6

vg_aes_gcm_prepare_vpclmul:
	mov rax, 16
	mov QWORD PTR [rdi+1024], rax
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
	vinserti128 ymm1, ymm1, xmm1, 1
	vpclmulqdq ymm8, ymm3, ymm3, 0
	vpclmulqdq ymm10, ymm3, ymm3, 17
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm4, ymm10, ymm8
	vinserti128 ymm12, ymm4, xmm3, 1
	vinserti128 ymm7, ymm4, xmm4, 1
	vmovdqu YMMWORD PTR [rdi+256], ymm12
	vpclmulqdq ymm8, ymm12, ymm7, 0
	vpclmulqdq ymm10, ymm12, ymm7, 17
	vpclmulqdq ymm9, ymm12, ymm7, 1
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm13, ymm10, ymm9
	vpclmulqdq ymm8, ymm7, ymm7, 0
	vpclmulqdq ymm10, ymm7, ymm7, 17
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm2, ymm10, ymm8
	vmovdqu YMMWORD PTR [rdi+288], ymm13
	vpclmulqdq ymm8, ymm12, ymm2, 0
	vpclmulqdq ymm10, ymm12, ymm2, 17
	vpclmulqdq ymm9, ymm12, ymm2, 1
	vpclmulqdq ymm11, ymm12, ymm2, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm14, ymm10, ymm9
	vpclmulqdq ymm8, ymm13, ymm2, 0
	vpclmulqdq ymm10, ymm13, ymm2, 17
	vpclmulqdq ymm9, ymm13, ymm2, 1
	vpclmulqdq ymm11, ymm13, ymm2, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm15, ymm10, ymm9
	vpclmulqdq ymm8, ymm2, ymm2, 0
	vpclmulqdq ymm10, ymm2, ymm2, 17
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm7, ymm10, ymm8
	vmovdqu YMMWORD PTR [rdi+320], ymm14
	vmovdqu YMMWORD PTR [rdi+352], ymm15
	vpclmulqdq ymm8, ymm12, ymm7, 0
	vpclmulqdq ymm10, ymm12, ymm7, 17
	vpclmulqdq ymm9, ymm12, ymm7, 1
	vpclmulqdq ymm11, ymm12, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm6, ymm10, ymm9
	vmovdqu YMMWORD PTR [rdi+384], ymm6
	vpclmulqdq ymm8, ymm13, ymm7, 0
	vpclmulqdq ymm10, ymm13, ymm7, 17
	vpclmulqdq ymm9, ymm13, ymm7, 1
	vpclmulqdq ymm11, ymm13, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm5, ymm10, ymm9
	vmovdqu YMMWORD PTR [rdi+416], ymm5
	vpclmulqdq ymm8, ymm14, ymm7, 0
	vpclmulqdq ymm10, ymm14, ymm7, 17
	vpclmulqdq ymm9, ymm14, ymm7, 1
	vpclmulqdq ymm11, ymm14, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm4, ymm10, ymm9
	vmovdqu YMMWORD PTR [rdi+448], ymm4
	vpclmulqdq ymm8, ymm15, ymm7, 0
	vpclmulqdq ymm10, ymm15, ymm7, 17
	vpclmulqdq ymm9, ymm15, ymm7, 1
	vpclmulqdq ymm11, ymm15, ymm7, 16
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm8, ymm1, 16
	vpshufd ymm8, ymm8, 78
	vpxor ymm8, ymm8, ymm11
	vpxor ymm9, ymm9, ymm8
	vpclmulqdq ymm11, ymm9, ymm1, 16
	vpshufd ymm9, ymm9, 78
	vpxor ymm9, ymm9, ymm11
	vpxor ymm3, ymm10, ymm9
	vmovdqu YMMWORD PTR [rdi+480], ymm3
	vzeroupper
	ret
	.p2align 6

vg_aes_gcm_prepare_pclmul_avx:
	mov rax, 16
	mov QWORD PTR [rdi+1024], rax
	movabs rax, 579005069656919567
	vmovq xmm0, rax
	movabs rax, 283686952306183
	vmovq xmm12, rax
	vpunpcklqdq xmm0, xmm0, xmm12
	movabs rax, 0
	vmovq xmm1, rax
	movabs rax, -4467570830351532032
	vmovq xmm12, rax
	vpunpcklqdq xmm1, xmm1, xmm12
	vmovdqu xmm7, XMMWORD PTR [rdi+240]
	vpshufb xmm7, xmm7, xmm0
	movabs rax, 1
	vmovq xmm13, rax
	movabs rax, -4467570830351532032
	vmovq xmm12, rax
	vpunpcklqdq xmm13, xmm13, xmm12
	movabs rax, -1
	vmovq xmm14, rax
	vpunpcklqdq xmm14, xmm14, xmm14
	vpsllq xmm3, xmm7, 1
	vpsrlq xmm11, xmm7, 63
	vpslldq xmm11, xmm11, 8
	vpor xmm3, xmm3, xmm11
	vpshufd xmm11, xmm7, 255
	vpsrld xmm11, xmm11, 31
	vpaddd xmm11, xmm11, xmm14
	vpandn xmm11, xmm11, xmm13
	vpxor xmm3, xmm3, xmm11
	vmovdqu XMMWORD PTR [rdi+272], xmm3
	vpclmulqdq xmm8, xmm3, xmm3, 0
	vpclmulqdq xmm10, xmm3, xmm3, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm4, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+256], xmm4
	vpclmulqdq xmm8, xmm4, xmm3, 0
	vpclmulqdq xmm10, xmm4, xmm3, 17
	vpclmulqdq xmm9, xmm4, xmm3, 1
	vpclmulqdq xmm11, xmm4, xmm3, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm5, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+304], xmm5
	vpclmulqdq xmm8, xmm4, xmm4, 0
	vpclmulqdq xmm10, xmm4, xmm4, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm6, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+288], xmm6
	vpclmulqdq xmm8, xmm6, xmm3, 0
	vpclmulqdq xmm10, xmm6, xmm3, 17
	vpclmulqdq xmm9, xmm6, xmm3, 1
	vpclmulqdq xmm11, xmm6, xmm3, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm12, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+336], xmm12
	vpclmulqdq xmm8, xmm5, xmm5, 0
	vpclmulqdq xmm10, xmm5, xmm5, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm13, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+320], xmm13
	vpclmulqdq xmm8, xmm6, xmm5, 0
	vpclmulqdq xmm10, xmm6, xmm5, 17
	vpclmulqdq xmm9, xmm6, xmm5, 1
	vpclmulqdq xmm11, xmm6, xmm5, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm14, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+368], xmm14
	vpclmulqdq xmm8, xmm6, xmm6, 0
	vpclmulqdq xmm10, xmm6, xmm6, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm15, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+352], xmm15
	vpclmulqdq xmm8, xmm15, xmm3, 0
	vpclmulqdq xmm10, xmm15, xmm3, 17
	vpclmulqdq xmm9, xmm15, xmm3, 1
	vpclmulqdq xmm11, xmm15, xmm3, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm2, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+400], xmm2
	vpclmulqdq xmm8, xmm12, xmm12, 0
	vpclmulqdq xmm10, xmm12, xmm12, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm4, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+384], xmm4
	vpclmulqdq xmm8, xmm15, xmm5, 0
	vpclmulqdq xmm10, xmm15, xmm5, 17
	vpclmulqdq xmm9, xmm15, xmm5, 1
	vpclmulqdq xmm11, xmm15, xmm5, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm6, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+432], xmm6
	vpclmulqdq xmm8, xmm13, xmm13, 0
	vpclmulqdq xmm10, xmm13, xmm13, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm7, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+416], xmm7
	vpclmulqdq xmm8, xmm15, xmm12, 0
	vpclmulqdq xmm10, xmm15, xmm12, 17
	vpclmulqdq xmm9, xmm15, xmm12, 1
	vpclmulqdq xmm11, xmm15, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm0, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+464], xmm0
	vpclmulqdq xmm8, xmm14, xmm14, 0
	vpclmulqdq xmm10, xmm14, xmm14, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm2, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+448], xmm2
	vpclmulqdq xmm8, xmm15, xmm14, 0
	vpclmulqdq xmm10, xmm15, xmm14, 17
	vpclmulqdq xmm9, xmm15, xmm14, 1
	vpclmulqdq xmm11, xmm15, xmm14, 16
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm9, xmm9, xmm8
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm9, xmm9, xmm11
	vpxor xmm4, xmm10, xmm9
	vmovdqu XMMWORD PTR [rdi+496], xmm4
	vpclmulqdq xmm8, xmm15, xmm15, 0
	vpclmulqdq xmm10, xmm15, xmm15, 17
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm6, xmm10, xmm8
	vmovdqu XMMWORD PTR [rdi+480], xmm6
	ret
	.p2align 6

vg_aes_gcm_prepare:
	mov rax, 0
	mov QWORD PTR [rdi+1024], rax
	ret
	.p2align 6

vg_aes_gcm_wipe_prepared_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 22f
	vpxor xmm0, xmm0, xmm0
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	vmovdqu YMMWORD PTR [rdi+64], ymm0
	vmovdqu YMMWORD PTR [rdi+96], ymm0
	vmovdqu YMMWORD PTR [rdi+128], ymm0
	vmovdqu YMMWORD PTR [rdi+160], ymm0
	vmovdqu YMMWORD PTR [rdi+192], ymm0
	vmovdqu YMMWORD PTR [rdi+224], ymm0
	vzeroupper
23:
21:
	ret
22:
	vpxor xmm0, xmm0, xmm0
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	vmovdqu YMMWORD PTR [rdi+64], ymm0
	vmovdqu YMMWORD PTR [rdi+96], ymm0
	vmovdqu YMMWORD PTR [rdi+128], ymm0
	vmovdqu YMMWORD PTR [rdi+160], ymm0
	vmovdqu YMMWORD PTR [rdi+192], ymm0
	vmovdqu YMMWORD PTR [rdi+224], ymm0
	vmovdqu YMMWORD PTR [rdi+256], ymm0
	vmovdqu YMMWORD PTR [rdi+288], ymm0
	vmovdqu YMMWORD PTR [rdi+320], ymm0
	vmovdqu YMMWORD PTR [rdi+352], ymm0
	vmovdqu YMMWORD PTR [rdi+384], ymm0
	vmovdqu YMMWORD PTR [rdi+416], ymm0
	vmovdqu YMMWORD PTR [rdi+448], ymm0
	vmovdqu YMMWORD PTR [rdi+480], ymm0
	vzeroupper
	jmp 23b
20:
	vpxor xmm0, xmm0, xmm0
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+32], ymm0
	vmovdqu YMMWORD PTR [rdi+64], ymm0
	vmovdqu YMMWORD PTR [rdi+96], ymm0
	vmovdqu YMMWORD PTR [rdi+128], ymm0
	vmovdqu YMMWORD PTR [rdi+160], ymm0
	vmovdqu YMMWORD PTR [rdi+192], ymm0
	vmovdqu YMMWORD PTR [rdi+224], ymm0
	vmovdqu YMMWORD PTR [rdi+256], ymm0
	vmovdqu YMMWORD PTR [rdi+288], ymm0
	vmovdqu YMMWORD PTR [rdi+320], ymm0
	vmovdqu YMMWORD PTR [rdi+352], ymm0
	vmovdqu YMMWORD PTR [rdi+384], ymm0
	vmovdqu YMMWORD PTR [rdi+416], ymm0
	vmovdqu YMMWORD PTR [rdi+448], ymm0
	vmovdqu YMMWORD PTR [rdi+480], ymm0
	vmovdqu YMMWORD PTR [rdi+512], ymm0
	vmovdqu YMMWORD PTR [rdi+544], ymm0
	vmovdqu YMMWORD PTR [rdi+576], ymm0
	vmovdqu YMMWORD PTR [rdi+608], ymm0
	vmovdqu YMMWORD PTR [rdi+640], ymm0
	vmovdqu YMMWORD PTR [rdi+672], ymm0
	vmovdqu YMMWORD PTR [rdi+704], ymm0
	vmovdqu YMMWORD PTR [rdi+736], ymm0
	vmovdqu YMMWORD PTR [rdi+768], ymm0
	vmovdqu YMMWORD PTR [rdi+800], ymm0
	vmovdqu YMMWORD PTR [rdi+832], ymm0
	vmovdqu YMMWORD PTR [rdi+864], ymm0
	vmovdqu YMMWORD PTR [rdi+896], ymm0
	vmovdqu YMMWORD PTR [rdi+928], ymm0
	vmovdqu YMMWORD PTR [rdi+960], ymm0
	vmovdqu YMMWORD PTR [rdi+992], ymm0
	vzeroupper
	jmp 21b
	.p2align 6

vg_aes_gcm_wipe_prepared:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 22f
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+16], xmm0
	movdqu XMMWORD PTR [rdi+32], xmm0
	movdqu XMMWORD PTR [rdi+48], xmm0
	movdqu XMMWORD PTR [rdi+64], xmm0
	movdqu XMMWORD PTR [rdi+80], xmm0
	movdqu XMMWORD PTR [rdi+96], xmm0
	movdqu XMMWORD PTR [rdi+112], xmm0
	movdqu XMMWORD PTR [rdi+128], xmm0
	movdqu XMMWORD PTR [rdi+144], xmm0
	movdqu XMMWORD PTR [rdi+160], xmm0
	movdqu XMMWORD PTR [rdi+176], xmm0
	movdqu XMMWORD PTR [rdi+192], xmm0
	movdqu XMMWORD PTR [rdi+208], xmm0
	movdqu XMMWORD PTR [rdi+224], xmm0
	movdqu XMMWORD PTR [rdi+240], xmm0
23:
21:
	ret
22:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+16], xmm0
	movdqu XMMWORD PTR [rdi+32], xmm0
	movdqu XMMWORD PTR [rdi+48], xmm0
	movdqu XMMWORD PTR [rdi+64], xmm0
	movdqu XMMWORD PTR [rdi+80], xmm0
	movdqu XMMWORD PTR [rdi+96], xmm0
	movdqu XMMWORD PTR [rdi+112], xmm0
	movdqu XMMWORD PTR [rdi+128], xmm0
	movdqu XMMWORD PTR [rdi+144], xmm0
	movdqu XMMWORD PTR [rdi+160], xmm0
	movdqu XMMWORD PTR [rdi+176], xmm0
	movdqu XMMWORD PTR [rdi+192], xmm0
	movdqu XMMWORD PTR [rdi+208], xmm0
	movdqu XMMWORD PTR [rdi+224], xmm0
	movdqu XMMWORD PTR [rdi+240], xmm0
	movdqu XMMWORD PTR [rdi+256], xmm0
	movdqu XMMWORD PTR [rdi+272], xmm0
	movdqu XMMWORD PTR [rdi+288], xmm0
	movdqu XMMWORD PTR [rdi+304], xmm0
	movdqu XMMWORD PTR [rdi+320], xmm0
	movdqu XMMWORD PTR [rdi+336], xmm0
	movdqu XMMWORD PTR [rdi+352], xmm0
	movdqu XMMWORD PTR [rdi+368], xmm0
	movdqu XMMWORD PTR [rdi+384], xmm0
	movdqu XMMWORD PTR [rdi+400], xmm0
	movdqu XMMWORD PTR [rdi+416], xmm0
	movdqu XMMWORD PTR [rdi+432], xmm0
	movdqu XMMWORD PTR [rdi+448], xmm0
	movdqu XMMWORD PTR [rdi+464], xmm0
	movdqu XMMWORD PTR [rdi+480], xmm0
	movdqu XMMWORD PTR [rdi+496], xmm0
	jmp 23b
20:
	pxor xmm0, xmm0
	movdqu XMMWORD PTR [rdi], xmm0
	movdqu XMMWORD PTR [rdi+16], xmm0
	movdqu XMMWORD PTR [rdi+32], xmm0
	movdqu XMMWORD PTR [rdi+48], xmm0
	movdqu XMMWORD PTR [rdi+64], xmm0
	movdqu XMMWORD PTR [rdi+80], xmm0
	movdqu XMMWORD PTR [rdi+96], xmm0
	movdqu XMMWORD PTR [rdi+112], xmm0
	movdqu XMMWORD PTR [rdi+128], xmm0
	movdqu XMMWORD PTR [rdi+144], xmm0
	movdqu XMMWORD PTR [rdi+160], xmm0
	movdqu XMMWORD PTR [rdi+176], xmm0
	movdqu XMMWORD PTR [rdi+192], xmm0
	movdqu XMMWORD PTR [rdi+208], xmm0
	movdqu XMMWORD PTR [rdi+224], xmm0
	movdqu XMMWORD PTR [rdi+240], xmm0
	movdqu XMMWORD PTR [rdi+256], xmm0
	movdqu XMMWORD PTR [rdi+272], xmm0
	movdqu XMMWORD PTR [rdi+288], xmm0
	movdqu XMMWORD PTR [rdi+304], xmm0
	movdqu XMMWORD PTR [rdi+320], xmm0
	movdqu XMMWORD PTR [rdi+336], xmm0
	movdqu XMMWORD PTR [rdi+352], xmm0
	movdqu XMMWORD PTR [rdi+368], xmm0
	movdqu XMMWORD PTR [rdi+384], xmm0
	movdqu XMMWORD PTR [rdi+400], xmm0
	movdqu XMMWORD PTR [rdi+416], xmm0
	movdqu XMMWORD PTR [rdi+432], xmm0
	movdqu XMMWORD PTR [rdi+448], xmm0
	movdqu XMMWORD PTR [rdi+464], xmm0
	movdqu XMMWORD PTR [rdi+480], xmm0
	movdqu XMMWORD PTR [rdi+496], xmm0
	movdqu XMMWORD PTR [rdi+512], xmm0
	movdqu XMMWORD PTR [rdi+528], xmm0
	movdqu XMMWORD PTR [rdi+544], xmm0
	movdqu XMMWORD PTR [rdi+560], xmm0
	movdqu XMMWORD PTR [rdi+576], xmm0
	movdqu XMMWORD PTR [rdi+592], xmm0
	movdqu XMMWORD PTR [rdi+608], xmm0
	movdqu XMMWORD PTR [rdi+624], xmm0
	movdqu XMMWORD PTR [rdi+640], xmm0
	movdqu XMMWORD PTR [rdi+656], xmm0
	movdqu XMMWORD PTR [rdi+672], xmm0
	movdqu XMMWORD PTR [rdi+688], xmm0
	movdqu XMMWORD PTR [rdi+704], xmm0
	movdqu XMMWORD PTR [rdi+720], xmm0
	movdqu XMMWORD PTR [rdi+736], xmm0
	movdqu XMMWORD PTR [rdi+752], xmm0
	movdqu XMMWORD PTR [rdi+768], xmm0
	movdqu XMMWORD PTR [rdi+784], xmm0
	movdqu XMMWORD PTR [rdi+800], xmm0
	movdqu XMMWORD PTR [rdi+816], xmm0
	movdqu XMMWORD PTR [rdi+832], xmm0
	movdqu XMMWORD PTR [rdi+848], xmm0
	movdqu XMMWORD PTR [rdi+864], xmm0
	movdqu XMMWORD PTR [rdi+880], xmm0
	movdqu XMMWORD PTR [rdi+896], xmm0
	movdqu XMMWORD PTR [rdi+912], xmm0
	movdqu XMMWORD PTR [rdi+928], xmm0
	movdqu XMMWORD PTR [rdi+944], xmm0
	movdqu XMMWORD PTR [rdi+960], xmm0
	movdqu XMMWORD PTR [rdi+976], xmm0
	movdqu XMMWORD PTR [rdi+992], xmm0
	movdqu XMMWORD PTR [rdi+1008], xmm0
	jmp 21b
	.p2align 6

vg_aes_gcm_init_aesni:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+128], rbx
	mov QWORD PTR [rcx+136], rbp
	mov QWORD PTR [rcx+144], r12
	mov QWORD PTR [rcx+152], r13
	mov QWORD PTR [rcx+160], r14
	mov QWORD PTR [rcx+168], r15
	mov r15, rcx
	mov r13, rdx
	mov rbx, rsi
	shr rbx, 2
	add rbx, 6
	mov rcx, r15
	add rcx, 512
	call {vg_aes_expand_key_scratch_aesni}
	mov eax, 0
	mov QWORD PTR [r13+240], rax
	mov QWORD PTR [r13+248], rax
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	mov rsi, rbx
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	add rcx, 240
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_init:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+128], rbx
	mov QWORD PTR [rcx+136], rbp
	mov QWORD PTR [rcx+144], r12
	mov QWORD PTR [rcx+152], r13
	mov QWORD PTR [rcx+160], r14
	mov QWORD PTR [rcx+168], r15
	mov r15, rcx
	mov r13, rdx
	mov rbx, rsi
	shr rbx, 2
	add rbx, 6
	mov rcx, r15
	add rcx, 512
	call {vg_aes_expand_key_scratch}
	mov eax, 0
	mov QWORD PTR [r13+240], rax
	mov QWORD PTR [r13+248], rax
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	mov rsi, rbx
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	add rcx, 240
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_init_vaes:
	lea rsp, [rsp-2568]
	mov rcx, rsp
	add rcx, 8
	mov QWORD PTR [rcx+128], rbx
	mov QWORD PTR [rcx+136], rbp
	mov QWORD PTR [rcx+144], r12
	mov QWORD PTR [rcx+152], r13
	mov QWORD PTR [rcx+160], r14
	mov QWORD PTR [rcx+168], r15
	mov r15, rcx
	mov r13, rdx
	mov rbx, rsi
	shr rbx, 2
	add rbx, 6
	mov rcx, r15
	add rcx, 512
	call {vg_aes_expand_key_scratch_aesni}
	mov eax, 0
	mov QWORD PTR [r13+240], rax
	mov QWORD PTR [r13+248], rax
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	mov rsi, rbx
	mov rdx, r15
	add rdx, 96
	mov rcx, r13
	add rcx, 240
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_aesni_pclmul:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_aesni_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_aesni:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_aesni:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_aesni_vpclmul:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_aesni_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_pclmul:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_vpclmul:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_vaes_pclmul:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_vaes_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_vaes:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_vaes:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_finish_vaes_vpclmul:
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 20f
	jmp 21f
20:
	mov rbx, rax
21:
	and rbx, 15
	test rbx, rbx
	je 22f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
24:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	ret
	.p2align 6

vg_aes_gcm_stream_verify_vaes_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov rbx, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+224], rbx
	mov rsi, r9
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 26f
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	jmp 27f
26:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
27:
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 29f
	jmp 210f
29:
	mov rbx, rax
210:
	and rbx, 15
	test rbx, rbx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 212f
211:
212:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 0
	mov rcx, rbx
	cmp rcx, 16
	je 214f
	mov r10d, 0
216:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 216b
	jmp 215f
214:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
215:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_aesni:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_aesni:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_aesni:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_aesni}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_aesni:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_aesni:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_aesni:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_aesni}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_aesni}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_aesni}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_aesni_pclmul:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_aesni_pclmul:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_aesni_pclmul:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_aesni_pclmul}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_aesni_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_aesni_pclmul:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_pclmul}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_aesni_pclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_aesni_pclmul}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_aesni_pclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni_pclmul}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni_pclmul}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_aesni_pclmul_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 22f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 24f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
	mov rcx, rbp
	test rcx, rcx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
27:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
23:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 212f
211:
212:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 215f
214:
215:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
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
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 216f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 219f
218:
219:
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 220f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 222f
224:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 224b
	jmp 223f
222:
223:
	test rcx, 15
	je 225f
	test rcx, 12
	je 227f
	test rcx, 8
	je 229f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 230f
229:
230:
	test rcx, 4
	je 231f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 232f
231:
232:
	test rcx, 3
	je 233f
235:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 235b
	jmp 234f
233:
234:
	jmp 228f
227:
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
228:
	jmp 226f
225:
226:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 221f
220:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
221:
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
21:
	ret
20:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov eax, 0
	cmp rbp, 12
	jne 237f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 239f
	mov eax, 1
	jmp 240f
239:
240:
	jmp 238f
237:
238:
	test rax, rax
	je 241f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rcx, QWORD PTR [r15+184]
	test rcx, rcx
	je 243f
	cmp rcx, 5
	je 245f
	cmp rcx, 16
	je 247f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
249:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 249b
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r15+96]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
	jmp 248f
247:
	mov rsi, QWORD PTR [r15+232]
	movdqu xmm7, XMMWORD PTR [rsi]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
248:
	jmp 246f
245:
	mov rsi, QWORD PTR [r15+232]
	mov eax, DWORD PTR [rsi]
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 32
	add rax, r10
	movq xmm7, rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
246:
	jmp 244f
243:
244:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 250f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 251f
250:
251:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 252f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 254f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 255f
254:
255:
	jmp 253f
252:
253:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 256f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 258f
260:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 260b
	jmp 259f
258:
259:
	test rcx, 15
	je 261f
	test rcx, 12
	je 263f
	test rcx, 8
	je 265f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 266f
265:
266:
	test rcx, 4
	je 267f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 268f
267:
268:
	test rcx, 3
	je 269f
271:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 271b
	jmp 270f
269:
270:
	jmp 264f
263:
272:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 272b
264:
	jmp 262f
261:
262:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 257f
256:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
257:
	jmp 242f
241:
	cmp rbp, 12
	je 273f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 275f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 276f
275:
276:
	mov rcx, rbp
	test rcx, rcx
	je 277f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
279:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 279b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 278f
277:
278:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 274f
273:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
274:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 280f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 281f
280:
281:
	mov rcx, rbp
	test rcx, rcx
	je 282f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 283f
282:
283:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 285f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 286f
285:
286:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
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
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 287f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 289f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 290f
289:
290:
	jmp 288f
287:
288:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 291f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 293f
295:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 295b
	jmp 294f
293:
294:
	test rcx, 15
	je 296f
	test rcx, 12
	je 298f
	test rcx, 8
	je 2100f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2101f
2100:
2101:
	test rcx, 4
	je 2102f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2103f
2102:
2103:
	test rcx, 3
	je 2104f
2106:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2106b
	jmp 2105f
2104:
2105:
	jmp 299f
298:
2107:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2107b
299:
	jmp 297f
296:
297:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 292f
291:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
292:
242:
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	jmp 21b
	.p2align 6

vg_aes_gcm_open_prepared_aesni_pclmul_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 22f
	cmp rbx, 17
	jb 24f
	jmp 25f
24:
	mov ecx, 1
25:
	jmp 23f
22:
23:
	test rcx, rcx
	je 26f
	cmp rbp, 12
	je 28f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 210f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 211f
210:
211:
	mov rcx, rbp
	test rcx, rcx
	je 212f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
214:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 214b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 213f
212:
213:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 29f
28:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
29:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 215f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 216f
215:
216:
	mov rcx, rbp
	test rcx, rcx
	je 217f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 220f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 221f
220:
221:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 222f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov rcx, rbp
	test rcx, rcx
	je 224f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
226:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 226b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 225f
224:
225:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 227f
	mov r10d, 0
229:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 229b
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
228:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 230f
	mov r10d, 0
232:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 232b
	jmp 231f
230:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
231:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 233f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 235f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 236f
235:
236:
	test rbp, rbp
	je 237f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
239:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	jmp 238f
237:
238:
	jmp 234f
233:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 240f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 241f
240:
241:
234:
	mov rax, QWORD PTR [r15+216]
	jmp 27f
26:
	mov eax, 0
27:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
21:
	ret
20:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 242f
	cmp rbx, 17
	jb 244f
	jmp 245f
244:
	mov ecx, 1
245:
	jmp 243f
242:
243:
	test rcx, rcx
	je 246f
	mov eax, 0
	cmp rbp, 12
	jne 248f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 250f
	mov eax, 1
	jmp 251f
250:
251:
	jmp 249f
248:
249:
	test rax, rax
	je 252f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rcx, QWORD PTR [r15+184]
	test rcx, rcx
	je 254f
	cmp rcx, 5
	je 256f
	cmp rcx, 16
	je 258f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
260:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 260b
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r15+96]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
	jmp 259f
258:
	mov rsi, QWORD PTR [r15+232]
	movdqu xmm7, XMMWORD PTR [rsi]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
259:
	jmp 257f
256:
	mov rsi, QWORD PTR [r15+232]
	mov eax, DWORD PTR [rsi]
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 32
	add rax, r10
	movq xmm7, rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
257:
	jmp 255f
254:
255:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 261f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 262f
261:
262:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 263f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
265:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 265b
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	jmp 264f
263:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
264:
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 266f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 268f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 269f
268:
269:
	jmp 267f
266:
267:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+12], esi
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 270f
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
	jmp 271f
270:
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
271:
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 272f
	mov r10d, 0
274:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 274b
	jmp 273f
272:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
273:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 275f
	mov r10d, 0
277:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 277b
	jmp 276f
275:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
276:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 278f
	mov rcx, QWORD PTR [r15+208]
	test rcx, rcx
	je 280f
	mov rdi, QWORD PTR [r15+200]
	mov rsi, r15
	add rsi, 1040
	mov r10d, 0
282:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 282b
	jmp 281f
280:
281:
	jmp 279f
278:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 283f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 284f
283:
284:
279:
	mov rax, QWORD PTR [r15+216]
	jmp 253f
252:
	cmp rbp, 12
	je 285f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 287f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 288f
287:
288:
	mov rcx, rbp
	test rcx, rcx
	je 289f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 290f
289:
290:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 286f
285:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
286:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 292f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 293f
292:
293:
	mov rcx, rbp
	test rcx, rcx
	je 294f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 295f
294:
295:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 297f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 298f
297:
298:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 2102f
2101:
2102:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 2104f
	mov r10d, 0
2106:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2106b
	jmp 2105f
2104:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2105:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 2107f
	mov r10d, 0
2109:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2109b
	jmp 2108f
2107:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2108:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 2110f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 2112f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 2113f
2112:
2113:
	test rbp, rbp
	je 2114f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2116:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2116b
	jmp 2115f
2114:
2115:
	jmp 2111f
2110:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 2117f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 2118f
2117:
2118:
2111:
	mov rax, QWORD PTR [r15+216]
253:
	jmp 247f
246:
	mov eax, 0
247:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	jmp 21b
	.p2align 6

vg_aes_gcm_open_to_prepared_aesni_pclmul_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_aesni_pclmul_avx}
	test eax, eax
	je 22f
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 24f
26:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
23:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
21:
	ret
20:
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+96]
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	cmp rcx, 64
	jb 27f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu YMMWORD PTR [rdi], ymm0
	mov r10d, 0
	sub r10, rdi
	and r10, 31
	mov r8, rcx
	sub r8, 64
	cmp r8, r10
	jb 29f
211:
	vmovdqu ymm0, YMMWORD PTR [rsi+r10*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+r10*1+32]
	vmovdqu YMMWORD PTR [rdi+r10*1], ymm0
	vmovdqu YMMWORD PTR [rdi+r10*1+32], ymm1
	add r10, 64
	cmp r8, r10
	jae 211b
	jmp 210f
29:
210:
	vmovdqu ymm0, YMMWORD PTR [rsi+rcx*1-64]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi+rcx*1-64], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 28f
27:
	cmp rcx, 32
	jb 212f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 213f
212:
	cmp rcx, 16
	jb 214f
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	vmovdqu XMMWORD PTR [rdi], xmm0
	vmovdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 215f
214:
	cmp rcx, 8
	jb 216f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 217f
216:
	cmp rcx, 4
	jb 218f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 219f
218:
	mov r10d, 0
	cmp r10, rcx
	je 220f
222:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	jmp 221f
220:
221:
219:
217:
215:
213:
28:
	vzeroupper
	mov rdi, QWORD PTR [rsp+80]
	mov rsi, QWORD PTR [rsp+72]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+40]
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	call {vg_aes_gcm_open_prepared_aesni_pclmul_avx}
	test eax, eax
	je 223f
	jmp 224f
223:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 225f
227:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
226:
224:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	jmp 21b
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_aesni_pclmul_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 223f
	jmp 224f
223:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
224:
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 225f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	jmp 230f
229:
230:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 234f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 235f
234:
235:
	test rbp, rbp
	je 236f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 246f
	jmp 247f
246:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
247:
	jmp 242f
241:
242:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 248f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 249f
248:
249:
	mov rcx, rbp
	test rcx, rcx
	je 250f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 240f
239:
240:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 271f
	jmp 272f
271:
	mov rcx, rbp
272:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 274f
	jmp 275f
274:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
275:
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 276f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	jmp 281f
280:
281:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 285f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 286f
285:
286:
	test rbp, rbp
	je 287f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
289:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	jmp 288f
287:
288:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 290f
	test rbx, rbx
	je 292f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 294f
	jmp 295f
294:
	mov rcx, rbp
295:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 297f
	jmp 298f
297:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
298:
	jmp 293f
292:
293:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 291f
290:
291:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_aesni_pclmul_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 220f
	jmp 221f
220:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
221:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 222f
	jmp 223f
222:
	mov rcx, rbp
223:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	add r12, rcx
	sub rbp, rcx
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 225f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 234f
	jmp 235f
234:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
235:
	jmp 230f
229:
230:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 236f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 237f
236:
237:
	mov rcx, rbp
	test rcx, rcx
	je 238f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
240:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 240b
	jmp 239f
238:
239:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 241f
	test rbx, rbx
	je 243f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 245f
	jmp 246f
245:
	mov rcx, rbp
246:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
247:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 247b
	add r12, rcx
	sub rbp, rcx
	jmp 244f
243:
244:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 248f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 249f
248:
249:
	test rbp, rbp
	je 250f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 242f
241:
242:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 271f
	jmp 272f
271:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
272:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 273f
	jmp 274f
273:
	mov rcx, rbp
274:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
275:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 275b
	add r12, rcx
	sub rbp, rcx
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 276f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared16_aesni_pclmul_avx}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 285f
	jmp 286f
285:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
286:
	jmp 281f
280:
281:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 287f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 288f
287:
288:
	mov rcx, rbp
	test rcx, rcx
	je 289f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
	jmp 290f
289:
290:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 292f
	test rbx, rbx
	je 294f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 296f
	jmp 297f
296:
	mov rcx, rbp
297:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
298:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 298b
	add r12, rcx
	sub rbp, rcx
	jmp 295f
294:
295:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 299f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 2100f
299:
2100:
	test rbp, rbp
	je 2101f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 293f
292:
293:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6

vg_aes_gcm_seal_gather_prepared_aesni_pclmul_avx:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 384
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 3072
	jb 24f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 26f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 27f
26:
27:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 3072
	jmp 25f
24:
25:
	jb 28f
	call {vg_aes_gcm_stream_init_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 210f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 212f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_pclmul}
	jmp 213f
212:
213:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 214f
216:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 216b
	jmp 215f
214:
215:
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_aesni_pclmul}
	jmp 29f
28:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 217f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 384
	jb 219f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 221f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 222f
221:
222:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 223f
225:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 226f
228:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 228b
	jmp 227f
226:
227:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 229f
231:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 231b
	jmp 230f
229:
230:
	cmp r10, rcx
	je 232f
	cmp rcx, 16
	jb 234f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 235f
234:
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
235:
	jmp 233f
232:
233:
	add rdi, rcx
	sub r9, 1
	jne 225b
	jmp 224f
223:
224:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 220f
219:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 237f
239:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 240f
242:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 242b
	jmp 241f
240:
241:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 243f
245:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 245b
	jmp 244f
243:
244:
	cmp r10, rcx
	je 246f
	cmp rcx, 16
	jb 248f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 249f
248:
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
249:
	jmp 247f
246:
247:
	add rdi, rcx
	sub r9, 1
	jne 239b
	jmp 238f
237:
238:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
220:
29:
	jmp 23f
22:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 251f
253:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 254f
256:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 256b
	jmp 255f
254:
255:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 257f
259:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 259b
	jmp 258f
257:
258:
	cmp r10, rcx
	je 260f
	cmp rcx, 16
	jb 262f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 263f
262:
264:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 264b
263:
	jmp 261f
260:
261:
	add rdi, rcx
	sub r9, 1
	jne 253b
	jmp 252f
251:
252:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
23:
	lea rsp, [rsp+240]
21:
	ret
20:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, rcx
	sub r11, 12
	cmp r9, 17
	cmovae r11, r9
	mov rax, QWORD PTR [rsp+16]
	sub rax, 1
	cmp rax, 2
	cmovae r11, rax
	jae 265f
	mov r10, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [r10+8]
	mov rax, r10
	shr rax, 4
	shl rax, 4
	add rax, 16
	cmp rax, QWORD PTR [rsp+32]
	cmovae rax, r11
	or r11, rax
	mov rax, QWORD PTR [rsp+32]
	shr rax, 8
	cmp r10, 256
	cmovae rax, r11
	or r11, rax
	jmp 266f
265:
266:
	test r11, r11
	je 267f
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 384
	jb 269f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 3072
	jb 271f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 273f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 274f
273:
274:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 3072
	jmp 272f
271:
272:
	jb 275f
	push rax
	lea rsp, [rsp-2568]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov r14, rcx
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	cmp rbp, 12
	je 277f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 279f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 280f
279:
280:
	mov rcx, rbp
	test rcx, rcx
	je 281f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
283:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 283b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 282f
281:
282:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 278f
277:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
278:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	push rax
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 284f
	test rbx, rbx
	je 286f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 288f
	jmp 289f
288:
	mov rcx, rbp
289:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
290:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 290b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 291f
	jmp 292f
291:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
292:
	jmp 287f
286:
287:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 293f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 294f
293:
294:
	mov rcx, rbp
	test rcx, rcx
	je 295f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
297:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 297b
	jmp 296f
295:
296:
	jmp 285f
284:
285:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 298f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 2100f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	push rax
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 2102f
	test rbx, rbx
	je 2104f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 2106f
	jmp 2107f
2106:
	mov rcx, rbp
2107:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2108:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2108b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 2109f
	jmp 2110f
2109:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
2110:
	jmp 2105f
2104:
2105:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2111f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 2112f
2111:
2112:
	mov rcx, rbp
	test rcx, rcx
	je 2113f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2115:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2115b
	jmp 2114f
2113:
2114:
	jmp 2103f
2102:
2103:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	pop rax
	jmp 2101f
2100:
2101:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 2116f
2118:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_prepared16_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 2118b
	jmp 2117f
2116:
2117:
	jmp 299f
298:
299:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	push rax
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 2119f
	jmp 2120f
2119:
	mov rbx, rax
2120:
	and rbx, 15
	test rbx, rbx
	je 2121f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
2123:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2123b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 2122f
2121:
2122:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	pop rax
	jmp 276f
275:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 2124f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 2125f
2124:
2125:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 384
	jb 2126f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 2128f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 2129f
2128:
2129:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 2130f
2132:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2133f
2135:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2135b
	jmp 2134f
2133:
2134:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2136f
2138:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2138b
	jmp 2137f
2136:
2137:
	cmp r10, rcx
	je 2139f
	cmp rcx, 16
	jb 2141f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2142f
2141:
2143:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2143b
2142:
	jmp 2140f
2139:
2140:
	add rdi, rcx
	sub r9, 1
	jne 2132b
	jmp 2131f
2130:
2131:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_prepared16_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 2127f
2126:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 2144f
2146:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2147f
2149:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2149b
	jmp 2148f
2147:
2148:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2150f
2152:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2152b
	jmp 2151f
2150:
2151:
	cmp r10, rcx
	je 2153f
	cmp rcx, 16
	jb 2155f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2156f
2155:
2157:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2157b
2156:
	jmp 2154f
2153:
2154:
	add rdi, rcx
	sub r9, 1
	jne 2146b
	jmp 2145f
2144:
2145:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_prepared_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
2127:
276:
	jmp 270f
269:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 2158f
2160:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2161f
2163:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2163b
	jmp 2162f
2161:
2162:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2164f
2166:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2166b
	jmp 2165f
2164:
2165:
	cmp r10, rcx
	je 2167f
	cmp rcx, 16
	jb 2169f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2170f
2169:
2171:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2171b
2170:
	jmp 2168f
2167:
2168:
	add rdi, rcx
	sub r9, 1
	jne 2160b
	jmp 2159f
2158:
2159:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_prepared_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
270:
	jmp 268f
267:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	cmp rax, 1
	je 2172f
	mov rcx, QWORD PTR [r10+24]
	test rcx, rcx
	je 2174f
	mov rsi, QWORD PTR [r10+16]
	mov rdi, QWORD PTR [rsp+24]
	add rdi, QWORD PTR [r10+8]
	mov r10d, 0
2176:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2176b
	jmp 2175f
2174:
2175:
	jmp 2173f
2172:
2173:
	mov ecx, 12
	mov r10, QWORD PTR [rsp+8]
	mov rsi, QWORD PTR [r10]
	mov rdi, QWORD PTR [r10+8]
	mov rax, QWORD PTR [rsp+40]
	mov r10, QWORD PTR [rsp+32]
	mov r11, QWORD PTR [rsp+24]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_prepared16_aesni_pclmul_avx}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
268:
	lea rsp, [rsp+240]
	jmp 21b
	.p2align 6

vg_aes_gcm_seal_prepared_aesni_vpclmul:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_aesni_vpclmul:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_aesni_vpclmul:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_aesni_vpclmul}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_aesni_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_aesni_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_aesni_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_aesni_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_aesni}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_aesni_vpclmul:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_vpclmul}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_aesni_vpclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_aesni_vpclmul}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_aesni_vpclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni_vpclmul}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_aesni_vpclmul}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_pclmul:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_pclmul:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_pclmul:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_pclmul}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_pclmul:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_pclmul}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_pclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_pclmul}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_pclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_pclmul}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_pclmul}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_vaes:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_vaes:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_vaes:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_vaes}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_vaes:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_vaes:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_vaes:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_vaes}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_vaes}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_vaes}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_vaes_pclmul:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_vaes_pclmul:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_vaes_pclmul:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_vaes_pclmul}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_vaes_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_vaes_pclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes_pclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_vaes_pclmul:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_pclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_pclmul}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_vaes_pclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_vaes_pclmul}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_vaes_pclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes_pclmul}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes_pclmul}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_seal_prepared_vaes_vpclmul:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 22f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 24f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
	mov rcx, rbp
	test rcx, rcx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
23:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 212f
211:
212:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 215f
214:
215:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 216f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 217f
216:
217:
	test rbp, rbp
	je 218f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 221f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 222f
221:
222:
	mov rcx, rbp
	test rcx, rcx
	je 223f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 225b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 224f
223:
224:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
21:
	ret
20:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 226f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 228f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 229f
228:
229:
	mov rcx, rbp
	test rcx, rcx
	je 230f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
232:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 232b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 231f
230:
231:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 227f
226:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
227:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 233f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 234f
233:
234:
	mov rcx, rbp
	test rcx, rcx
	je 235f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 236f
235:
236:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 239f
238:
239:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 240f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 241f
240:
241:
	test rbp, rbp
	je 242f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
244:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 244b
	jmp 243f
242:
243:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 245f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 246f
245:
246:
	mov rcx, rbp
	test rcx, rcx
	je 247f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
249:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 249b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 248f
247:
248:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	jmp 21b
	.p2align 6

vg_aes_gcm_open_prepared_vaes_vpclmul:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 22f
	cmp rbx, 17
	jb 24f
	jmp 25f
24:
	mov ecx, 1
25:
	jmp 23f
22:
23:
	test rcx, rcx
	je 26f
	cmp rbp, 12
	je 28f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 210f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 211f
210:
211:
	mov rcx, rbp
	test rcx, rcx
	je 212f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
214:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 214b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 213f
212:
213:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 29f
28:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
29:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 215f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 216f
215:
216:
	mov rcx, rbp
	test rcx, rcx
	je 217f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 220f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 221f
220:
221:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 222f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 223f
222:
223:
	mov rcx, rbp
	test rcx, rcx
	je 224f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
226:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 226b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 225f
224:
225:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 227f
	mov r10d, 0
229:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 229b
	jmp 228f
227:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
228:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 230f
	mov r10d, 0
232:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 232b
	jmp 231f
230:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
231:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 233f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 235f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 236f
235:
236:
	test rbp, rbp
	je 237f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
239:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	jmp 238f
237:
238:
	jmp 234f
233:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 240f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 241f
240:
241:
234:
	mov rax, QWORD PTR [r15+216]
	jmp 27f
26:
	mov eax, 0
27:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
21:
	ret
20:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 242f
	cmp rbx, 17
	jb 244f
	jmp 245f
244:
	mov ecx, 1
245:
	jmp 243f
242:
243:
	test rcx, rcx
	je 246f
	mov eax, 0
	cmp rbp, 12
	jne 248f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 250f
	mov eax, 1
	jmp 251f
250:
251:
	jmp 249f
248:
249:
	test rax, rax
	je 252f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rcx, QWORD PTR [r15+184]
	test rcx, rcx
	je 254f
	cmp rcx, 5
	je 256f
	cmp rcx, 16
	je 258f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
260:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 260b
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r15+96]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
	jmp 259f
258:
	mov rsi, QWORD PTR [r15+232]
	movdqu xmm7, XMMWORD PTR [rsi]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
259:
	jmp 257f
256:
	mov rsi, QWORD PTR [r15+232]
	mov eax, DWORD PTR [rsi]
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 32
	add rax, r10
	movq xmm7, rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
257:
	jmp 255f
254:
255:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 261f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared16_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 262f
261:
262:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 263f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
265:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 265b
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	jmp 264f
263:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
264:
	movdqu xmm5, XMMWORD PTR [r14]
	movdqu xmm7, XMMWORD PTR [r14+48]
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm5, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 266f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 268f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm5, xmm8
	aesenc xmm7, xmm8
	jmp 269f
268:
269:
	jmp 267f
266:
267:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm5, xmm8
	aesenclast xmm7, xmm8
	movdqu XMMWORD PTR [r15+1024], xmm5
	movdqu XMMWORD PTR [r15+1040], xmm7
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+12], esi
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 270f
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
	jmp 271f
270:
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
271:
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 272f
	mov r10d, 0
274:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 274b
	jmp 273f
272:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
273:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 275f
	mov r10d, 0
277:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 277b
	jmp 276f
275:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
276:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 278f
	mov rcx, QWORD PTR [r15+208]
	test rcx, rcx
	je 280f
	mov rdi, QWORD PTR [r15+200]
	mov rsi, r15
	add rsi, 1040
	mov r10d, 0
282:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 282b
	jmp 281f
280:
281:
	jmp 279f
278:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 283f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 284f
283:
284:
279:
	mov rax, QWORD PTR [r15+216]
	jmp 253f
252:
	cmp rbp, 12
	je 285f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 287f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 288f
287:
288:
	mov rcx, rbp
	test rcx, rcx
	je 289f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 290f
289:
290:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 286f
285:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
286:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 292f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 293f
292:
293:
	mov rcx, rbp
	test rcx, rcx
	je 294f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 295f
294:
295:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 297f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared16_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 298f
297:
298:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2102f
2101:
2102:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 2104f
	mov r10d, 0
2106:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2106b
	jmp 2105f
2104:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2105:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 2107f
	mov r10d, 0
2109:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2109b
	jmp 2108f
2107:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2108:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 2110f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 2112f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2113f
2112:
2113:
	test rbp, rbp
	je 2114f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2116:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2116b
	jmp 2115f
2114:
2115:
	jmp 2111f
2110:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 2117f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2118f
2117:
2118:
2111:
	mov rax, QWORD PTR [r15+216]
253:
	jmp 247f
246:
	mov eax, 0
247:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	jmp 21b
	.p2align 6

vg_aes_gcm_open_to_prepared_vaes_vpclmul:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_vaes_vpclmul}
	test eax, eax
	je 22f
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 24f
26:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
23:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
21:
	ret
20:
	mov rax, QWORD PTR [rsp+16]
	cmp rax, 1024
	jae 27f
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+96]
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	cmp rcx, 64
	jb 29f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu YMMWORD PTR [rdi], ymm0
	mov r10d, 0
	sub r10, rdi
	and r10, 31
	mov r8, rcx
	sub r8, 64
	cmp r8, r10
	jb 211f
213:
	vmovdqu ymm0, YMMWORD PTR [rsi+r10*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+r10*1+32]
	vmovdqu YMMWORD PTR [rdi+r10*1], ymm0
	vmovdqu YMMWORD PTR [rdi+r10*1+32], ymm1
	add r10, 64
	cmp r8, r10
	jae 213b
	jmp 212f
211:
212:
	vmovdqu ymm0, YMMWORD PTR [rsi+rcx*1-64]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi+rcx*1-64], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 210f
29:
	cmp rcx, 32
	jb 214f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 215f
214:
	cmp rcx, 16
	jb 216f
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	vmovdqu XMMWORD PTR [rdi], xmm0
	vmovdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 217f
216:
	cmp rcx, 8
	jb 218f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 219f
218:
	cmp rcx, 4
	jb 220f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 221f
220:
	mov r10d, 0
	cmp r10, rcx
	je 222f
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	jmp 223f
222:
223:
221:
219:
217:
215:
210:
	vzeroupper
	mov rdi, QWORD PTR [rsp+80]
	mov rsi, QWORD PTR [rsp+72]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+40]
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	call {vg_aes_gcm_open_prepared_vaes_vpclmul}
	test eax, eax
	je 225f
	jmp 226f
225:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 227f
229:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 229b
	jmp 228f
227:
228:
226:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
28:
	jmp 21b
27:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_prepared16_vaes_vpclmul}
	test eax, eax
	je 230f
	jmp 231f
230:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 232f
234:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	jmp 233f
232:
233:
231:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	jmp 28b
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 223f
	jmp 224f
223:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
224:
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 225f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	jmp 230f
229:
230:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 234f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 235f
234:
235:
	test rbp, rbp
	je 236f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 246f
	jmp 247f
246:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
247:
	jmp 242f
241:
242:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 248f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 249f
248:
249:
	mov rcx, rbp
	test rcx, rcx
	je 250f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 240f
239:
240:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 271f
	jmp 272f
271:
	mov rcx, rbp
272:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 274f
	jmp 275f
274:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
275:
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 276f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared16_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	jmp 281f
280:
281:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 285f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 286f
285:
286:
	test rbp, rbp
	je 287f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
289:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	jmp 288f
287:
288:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 290f
	test rbx, rbx
	je 292f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 294f
	jmp 295f
294:
	mov rcx, rbp
295:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 297f
	jmp 298f
297:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
298:
	jmp 293f
292:
293:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 291f
290:
291:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 220f
	jmp 221f
220:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
221:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 222f
	jmp 223f
222:
	mov rcx, rbp
223:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	add r12, rcx
	sub rbp, rcx
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 225f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 234f
	jmp 235f
234:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
235:
	jmp 230f
229:
230:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 236f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 237f
236:
237:
	mov rcx, rbp
	test rcx, rcx
	je 238f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
240:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 240b
	jmp 239f
238:
239:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 241f
	test rbx, rbx
	je 243f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 245f
	jmp 246f
245:
	mov rcx, rbp
246:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
247:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 247b
	add r12, rcx
	sub rbp, rcx
	jmp 244f
243:
244:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 248f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 249f
248:
249:
	test rbp, rbp
	je 250f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 242f
241:
242:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 271f
	jmp 272f
271:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
272:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 273f
	jmp 274f
273:
	mov rcx, rbp
274:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
275:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 275b
	add r12, rcx
	sub rbp, rcx
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 276f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared16_vaes_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 285f
	jmp 286f
285:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
286:
	jmp 281f
280:
281:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 287f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 288f
287:
288:
	mov rcx, rbp
	test rcx, rcx
	je 289f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
	jmp 290f
289:
290:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 292f
	test rbx, rbx
	je 294f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 296f
	jmp 297f
296:
	mov rcx, rbp
297:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
298:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 298b
	add r12, rcx
	sub rbp, rcx
	jmp 295f
294:
295:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 299f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2100f
299:
2100:
	test rbp, rbp
	je 2101f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 293f
292:
293:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6

vg_aes_gcm_seal_gather_prepared_vaes_vpclmul:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 16
	jae 20f
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 1024
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 16384
	jb 24f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 26f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 27f
26:
27:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 16384
	jmp 25f
24:
25:
	jb 28f
	call {vg_aes_gcm_stream_init_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 210f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 212f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_vpclmul}
	jmp 213f
212:
213:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 214f
216:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 216b
	jmp 215f
214:
215:
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_vaes_vpclmul}
	jmp 29f
28:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 217f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 1024
	jb 219f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 221f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 222f
221:
222:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 223f
225:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 226f
228:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 228b
	jmp 227f
226:
227:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 229f
231:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 231b
	jmp 230f
229:
230:
	cmp r10, rcx
	je 232f
	cmp rcx, 16
	jb 234f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 235f
234:
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
235:
	jmp 233f
232:
233:
	add rdi, rcx
	sub r9, 1
	jne 225b
	jmp 224f
223:
224:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 220f
219:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 237f
239:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 240f
242:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 242b
	jmp 241f
240:
241:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 243f
245:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 245b
	jmp 244f
243:
244:
	cmp r10, rcx
	je 246f
	cmp rcx, 16
	jb 248f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 249f
248:
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
249:
	jmp 247f
246:
247:
	add rdi, rcx
	sub r9, 1
	jne 239b
	jmp 238f
237:
238:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
220:
29:
	jmp 23f
22:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 251f
253:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 254f
256:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 256b
	jmp 255f
254:
255:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 257f
259:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 259b
	jmp 258f
257:
258:
	cmp r10, rcx
	je 260f
	cmp rcx, 16
	jb 262f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 263f
262:
264:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 264b
263:
	jmp 261f
260:
261:
	add rdi, rcx
	sub r9, 1
	jne 253b
	jmp 252f
251:
252:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
23:
	lea rsp, [rsp+240]
21:
	ret
20:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, rcx
	sub r11, 12
	cmp r9, 17
	cmovae r11, r9
	mov rax, QWORD PTR [rsp+16]
	sub rax, 1
	cmp rax, 2
	cmovae r11, rax
	jae 265f
	mov r10, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [r10+8]
	mov rax, r10
	shr rax, 4
	shl rax, 4
	add rax, 16
	cmp rax, QWORD PTR [rsp+32]
	cmovae rax, r11
	or r11, rax
	mov rax, QWORD PTR [rsp+32]
	shr rax, 8
	cmp r10, 256
	cmovae rax, r11
	or r11, rax
	jmp 266f
265:
266:
	test r11, r11
	je 267f
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 1024
	jb 269f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 16384
	jb 271f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 273f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 274f
273:
274:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 16384
	jmp 272f
271:
272:
	jb 275f
	push rax
	lea rsp, [rsp-2568]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov r14, rcx
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	cmp rbp, 12
	je 277f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 279f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 280f
279:
280:
	mov rcx, rbp
	test rcx, rcx
	je 281f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
283:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 283b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 282f
281:
282:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 278f
277:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
278:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	push rax
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 284f
	test rbx, rbx
	je 286f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 288f
	jmp 289f
288:
	mov rcx, rbp
289:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
290:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 290b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 291f
	jmp 292f
291:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
292:
	jmp 287f
286:
287:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 293f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 294f
293:
294:
	mov rcx, rbp
	test rcx, rcx
	je 295f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
297:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 297b
	jmp 296f
295:
296:
	jmp 285f
284:
285:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 298f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 2100f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	push rax
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 2102f
	test rbx, rbx
	je 2104f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 2106f
	jmp 2107f
2106:
	mov rcx, rbp
2107:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2108:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2108b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 2109f
	jmp 2110f
2109:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
2110:
	jmp 2105f
2104:
2105:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2111f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2112f
2111:
2112:
	mov rcx, rbp
	test rcx, rcx
	je 2113f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2115:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2115b
	jmp 2114f
2113:
2114:
	jmp 2103f
2102:
2103:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	pop rax
	jmp 2101f
2100:
2101:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 2116f
2118:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_prepared16_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 2118b
	jmp 2117f
2116:
2117:
	jmp 299f
298:
299:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	push rax
	lea rsp, [rsp-2576]
	mov rax, rsp
	add rax, 16
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbx, QWORD PTR [r15+192]
	mov rax, QWORD PTR [r15+184]
	test rbx, rbx
	je 2119f
	jmp 2120f
2119:
	mov rbx, rax
2120:
	and rbx, 15
	test rbx, rbx
	je 2121f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
2123:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2123b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2122f
2121:
2122:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, QWORD PTR [r15+200]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2576]
	pop rax
	jmp 276f
275:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 2124f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 2125f
2124:
2125:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 1024
	jb 2126f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 2128f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 2129f
2128:
2129:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 2130f
2132:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2133f
2135:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2135b
	jmp 2134f
2133:
2134:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2136f
2138:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2138b
	jmp 2137f
2136:
2137:
	cmp r10, rcx
	je 2139f
	cmp rcx, 16
	jb 2141f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2142f
2141:
2143:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2143b
2142:
	jmp 2140f
2139:
2140:
	add rdi, rcx
	sub r9, 1
	jne 2132b
	jmp 2131f
2130:
2131:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_prepared16_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 2127f
2126:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 2144f
2146:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2147f
2149:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2149b
	jmp 2148f
2147:
2148:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2150f
2152:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2152b
	jmp 2151f
2150:
2151:
	cmp r10, rcx
	je 2153f
	cmp rcx, 16
	jb 2155f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2156f
2155:
2157:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2157b
2156:
	jmp 2154f
2153:
2154:
	add rdi, rcx
	sub r9, 1
	jne 2146b
	jmp 2145f
2144:
2145:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_prepared_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
2127:
276:
	jmp 270f
269:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 2158f
2160:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2161f
2163:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2163b
	jmp 2162f
2161:
2162:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2164f
2166:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2166b
	jmp 2165f
2164:
2165:
	cmp r10, rcx
	je 2167f
	cmp rcx, 16
	jb 2169f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2170f
2169:
2171:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2171b
2170:
	jmp 2168f
2167:
2168:
	add rdi, rcx
	sub r9, 1
	jne 2160b
	jmp 2159f
2158:
2159:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_prepared_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
270:
	jmp 268f
267:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	cmp rax, 1
	je 2172f
	mov rcx, QWORD PTR [r10+24]
	test rcx, rcx
	je 2174f
	mov rsi, QWORD PTR [r10+16]
	mov rdi, QWORD PTR [rsp+24]
	add rdi, QWORD PTR [r10+8]
	mov r10d, 0
2176:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2176b
	jmp 2175f
2174:
2175:
	jmp 2173f
2172:
2173:
	mov ecx, 12
	mov r10, QWORD PTR [rsp+8]
	mov rsi, QWORD PTR [r10]
	mov rdi, QWORD PTR [r10+8]
	mov rax, QWORD PTR [rsp+40]
	mov r10, QWORD PTR [rsp+32]
	mov r11, QWORD PTR [rsp+24]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_prepared16_vaes_vpclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
268:
	lea rsp, [rsp+240]
	jmp 21b
	.p2align 6

vg_aes_gcm_seal_prepared_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov eax, 0
	cmp rbp, 12
	jne 22f
	mov rcx, QWORD PTR [r15+184]
	or rcx, QWORD PTR [r15+208]
	cmp rcx, 512
	jae 24f
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	add rcx, rdx
	cmp rcx, 32
	jae 26f
	mov rdx, QWORD PTR [r15+208]
	mov rcx, rdx
	shl rcx, 4
	add rcx, rdx
	add rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jb 28f
	mov eax, 1
	jmp 29f
28:
29:
	jmp 27f
26:
27:
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	test rax, rax
	je 210f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov QWORD PTR [r15+272], rcx
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	mov QWORD PTR [r15+280], rdx
	mov rax, rcx
	add rax, rdx
	add rax, 1
	mov r8, rax
	add r8, 3
	shr r8, 2
	shl r8, 2
	mov QWORD PTR [r15+288], r8
	sub r8, rax
	mov QWORD PTR [r15+296], r8
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
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
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
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
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
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
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	mov r11, r15
	add r11, 1536
	vinserti128 ymm8, ymm6, xmm5, 1
	vinserti128 ymm9, ymm4, xmm3, 1
	vshufi32x4 zmm8, zmm8, zmm9, 68
	vmovdqu32 ZMMWORD PTR [r11], zmm8
	vinserti128 ymm0, ymm0, xmm0, 1
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
	mov rax, QWORD PTR [r15+288]
	cmp rax, 5
	jb 212f
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
	vmovdqu32 ZMMWORD PTR [r11+64], zmm10
	cmp rax, 9
	jb 214f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+64]
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
	vmovdqu32 ZMMWORD PTR [r11+128], zmm10
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
	vmovdqu32 ZMMWORD PTR [r11+192], zmm10
	cmp rax, 17
	jb 216f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+192]
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
	jmp 217f
216:
217:
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	vpxord zmm2, zmm2, zmm2
	vmovdqu32 ZMMWORD PTR [r15+512], zmm2
	vmovdqu32 ZMMWORD PTR [r15+576], zmm2
	vmovdqu32 ZMMWORD PTR [r15+640], zmm2
	vmovdqu32 ZMMWORD PTR [r15+704], zmm2
	vmovdqu32 ZMMWORD PTR [r15+768], zmm2
	vmovdqu32 ZMMWORD PTR [r15+832], zmm2
	vmovdqu32 ZMMWORD PTR [r15+896], zmm2
	vmovdqu32 ZMMWORD PTR [r15+960], zmm2
	mov rdi, QWORD PTR [r15+296]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+232]
	mov rcx, QWORD PTR [r15+184]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 218f
220:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 220b
	jmp 219f
218:
219:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r14
	mov r8, r15
	add r8, 1024
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
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	mov r9, QWORD PTR [r15+280]
	add r9, 4
	shr r9, 2
221:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 10
	je 222f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 224f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 225f
224:
225:
	jmp 223f
222:
223:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 221b
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 226f
228:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 228b
	jmp 227f
226:
227:
	test rcx, 15
	je 229f
	test rcx, 12
	je 231f
	test rcx, 8
	je 233f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 234f
233:
234:
	test rcx, 4
	je 235f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 236f
235:
236:
	test rcx, 3
	je 237f
239:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 239b
	jmp 238f
237:
238:
	jmp 232f
231:
240:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 240b
232:
	jmp 230f
229:
230:
	mov rdi, QWORD PTR [r15+288]
	shl rdi, 4
	add rdi, r15
	add rdi, 496
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+208]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rdx, r15
	add rdx, 384
	mov r9, QWORD PTR [r15+288]
	shr r9, 2
	mov r11, r9
	shl r11, 6
	add r11, r15
	add r11, 1344
	vpxord zmm8, zmm8, zmm8
	vpxord zmm9, zmm9, zmm9
	vpxord zmm10, zmm10, zmm10
241:
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
	add rdx, 64
	sub r11, 64
	sub r9, 1
	jne 241b
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
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 211f
210:
	cmp rbp, 12
	je 242f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 244f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 245f
244:
245:
	mov rcx, rbp
	test rcx, rcx
	je 246f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 247f
246:
247:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 243f
242:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
243:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 249f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 250f
249:
250:
	mov rcx, rbp
	test rcx, rcx
	je 251f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
253:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 253b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 252f
251:
252:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 254f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 255f
254:
255:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
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
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 256f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 258f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 259f
258:
259:
	jmp 257f
256:
257:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 260f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 262f
264:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 264b
	jmp 263f
262:
263:
	test rcx, 15
	je 265f
	test rcx, 12
	je 267f
	test rcx, 8
	je 269f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 270f
269:
270:
	test rcx, 4
	je 271f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 272f
271:
272:
	test rcx, 3
	je 273f
275:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 275b
	jmp 274f
273:
274:
	jmp 268f
267:
276:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 276b
268:
	jmp 266f
265:
266:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 261f
260:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
261:
211:
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
21:
	ret
20:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov eax, 0
	cmp rbp, 12
	jne 277f
	mov rcx, QWORD PTR [r15+184]
	or rcx, QWORD PTR [r15+208]
	cmp rcx, 512
	jae 279f
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	add rcx, rdx
	cmp rcx, 32
	jae 281f
	mov rdx, QWORD PTR [r15+208]
	mov rcx, rdx
	shl rcx, 4
	add rcx, rdx
	add rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jb 283f
	mov eax, 1
	jmp 284f
283:
284:
	jmp 282f
281:
282:
	jmp 280f
279:
280:
	jmp 278f
277:
278:
	test rax, rax
	je 285f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov QWORD PTR [r15+272], rcx
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	mov QWORD PTR [r15+280], rdx
	mov rax, rcx
	add rax, rdx
	add rax, 1
	mov r8, rax
	add r8, 3
	shr r8, 2
	shl r8, 2
	mov QWORD PTR [r15+288], r8
	sub r8, rax
	mov QWORD PTR [r15+296], r8
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
	vpxord zmm2, zmm2, zmm2
	vmovdqu32 ZMMWORD PTR [r15+512], zmm2
	vmovdqu32 ZMMWORD PTR [r15+576], zmm2
	vmovdqu32 ZMMWORD PTR [r15+640], zmm2
	vmovdqu32 ZMMWORD PTR [r15+704], zmm2
	vmovdqu32 ZMMWORD PTR [r15+768], zmm2
	vmovdqu32 ZMMWORD PTR [r15+832], zmm2
	vmovdqu32 ZMMWORD PTR [r15+896], zmm2
	vmovdqu32 ZMMWORD PTR [r15+960], zmm2
	mov rdi, QWORD PTR [r15+296]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+232]
	mov rcx, QWORD PTR [r15+184]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 287f
289:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 289b
	jmp 288f
287:
288:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r14
	mov r8, r15
	add r8, 1024
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
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	mov r9, QWORD PTR [r15+280]
	add r9, 4
	shr r9, 2
290:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 10
	je 291f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 293f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 294f
293:
294:
	jmp 292f
291:
292:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 290b
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 295f
297:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 297b
	jmp 296f
295:
296:
	test rcx, 15
	je 298f
	test rcx, 12
	je 2100f
	test rcx, 8
	je 2102f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2103f
2102:
2103:
	test rcx, 4
	je 2104f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2105f
2104:
2105:
	test rcx, 3
	je 2106f
2108:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2108b
	jmp 2107f
2106:
2107:
	jmp 2101f
2100:
2109:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2109b
2101:
	jmp 299f
298:
299:
	mov rdi, QWORD PTR [r15+288]
	shl rdi, 4
	add rdi, r15
	add rdi, 496
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+208]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rdx, r15
	add rdx, 384
	mov r9, QWORD PTR [r15+288]
	shr r9, 2
	mov r11, r9
	shl r11, 6
	add r11, r13
	add r11, 64
	vpxord zmm8, zmm8, zmm8
	vpxord zmm9, zmm9, zmm9
	vpxord zmm10, zmm10, zmm10
2110:
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vshufi32x4 zmm12, zmm12, zmm12, 78
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	add rdx, 64
	sub r11, 64
	sub r9, 1
	jne 2110b
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
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 286f
285:
	mov eax, 0
	cmp rbp, 12
	jne 2111f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 2113f
	mov rcx, QWORD PTR [r15+208]
	cmp rcx, 256
	jb 2115f
	mov eax, 1
	jmp 2116f
2115:
2116:
	jmp 2114f
2113:
2114:
	jmp 2112f
2111:
2112:
	test rax, rax
	je 2117f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rcx, QWORD PTR [r15+184]
	test rcx, rcx
	je 2119f
	cmp rcx, 5
	je 2121f
	cmp rcx, 16
	je 2123f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
2125:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2125b
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r15+96]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
	jmp 2124f
2123:
	mov rsi, QWORD PTR [r15+232]
	movdqu xmm7, XMMWORD PTR [rsi]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
2124:
	jmp 2122f
2121:
	mov rsi, QWORD PTR [r15+232]
	mov eax, DWORD PTR [rsi]
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 32
	add rax, r10
	movq xmm7, rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
2122:
	jmp 2120f
2119:
2120:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 2126f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 2127f
2126:
2127:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 2128f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 2130f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 2131f
2130:
2131:
	jmp 2129f
2128:
2129:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 2132f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 2134f
2136:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 2136b
	jmp 2135f
2134:
2135:
	test rcx, 15
	je 2137f
	test rcx, 12
	je 2139f
	test rcx, 8
	je 2141f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2142f
2141:
2142:
	test rcx, 4
	je 2143f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2144f
2143:
2144:
	test rcx, 3
	je 2145f
2147:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2147b
	jmp 2146f
2145:
2146:
	jmp 2140f
2139:
2148:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2148b
2140:
	jmp 2138f
2137:
2138:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 2133f
2132:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
2133:
	jmp 2118f
2117:
	cmp rbp, 12
	je 2149f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2151f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2152f
2151:
2152:
	mov rcx, rbp
	test rcx, rcx
	je 2153f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2155:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2155b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2154f
2153:
2154:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2150f
2149:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
2150:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2156f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2157f
2156:
2157:
	mov rcx, rbp
	test rcx, rcx
	je 2158f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2160:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2160b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2159f
2158:
2159:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 2161f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 2162f
2161:
2162:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
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
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 2163f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 2165f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 2166f
2165:
2166:
	jmp 2164f
2163:
2164:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 2167f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 2169f
2171:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	vmovdqu XMMWORD PTR [rdi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 2171b
	jmp 2170f
2169:
2170:
	test rcx, 15
	je 2172f
	test rcx, 12
	je 2174f
	test rcx, 8
	je 2176f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	mov QWORD PTR [rdi+r10*1], rax
	add r10, 8
	jmp 2177f
2176:
2177:
	test rcx, 4
	je 2178f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	mov DWORD PTR [rdi+r10*1], eax
	add r10, 4
	jmp 2179f
2178:
2179:
	test rcx, 3
	je 2180f
2182:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2182b
	jmp 2181f
2180:
2181:
	jmp 2175f
2174:
2183:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2183b
2175:
	jmp 2173f
2172:
2173:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
	jmp 2168f
2167:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15], xmm2
	vzeroupper
2168:
2118:
286:
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	jmp 21b
	.p2align 6

vg_aes_gcm_open_prepared_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 22f
	cmp rbx, 17
	jb 24f
	jmp 25f
24:
	mov ecx, 1
25:
	jmp 23f
22:
23:
	test rcx, rcx
	je 26f
	mov eax, 0
	cmp rbp, 12
	jne 28f
	mov rcx, QWORD PTR [r15+184]
	or rcx, QWORD PTR [r15+208]
	cmp rcx, 512
	jae 210f
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	add rcx, rdx
	cmp rcx, 32
	jae 212f
	mov rdx, QWORD PTR [r15+208]
	mov rcx, rdx
	shl rcx, 4
	add rcx, rdx
	add rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jb 214f
	mov eax, 1
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	jmp 211f
210:
211:
	jmp 29f
28:
29:
	test rax, rax
	je 216f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov QWORD PTR [r15+272], rcx
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	mov QWORD PTR [r15+280], rdx
	mov rax, rcx
	add rax, rdx
	add rax, 1
	mov r8, rax
	add r8, 3
	shr r8, 2
	shl r8, 2
	mov QWORD PTR [r15+288], r8
	sub r8, rax
	mov QWORD PTR [r15+296], r8
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r13+240]
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
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
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
	movdqa xmm5, xmm10
	pxor xmm5, xmm8
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm4
	pclmulqdq xmm11, xmm4, 16
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
	movdqa xmm6, xmm10
	pxor xmm6, xmm8
	mov r11, r15
	add r11, 1536
	vinserti128 ymm8, ymm6, xmm5, 1
	vinserti128 ymm9, ymm4, xmm3, 1
	vshufi32x4 zmm8, zmm8, zmm9, 68
	vmovdqu32 ZMMWORD PTR [r11], zmm8
	vinserti128 ymm0, ymm0, xmm0, 1
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
	mov rax, QWORD PTR [r15+288]
	cmp rax, 5
	jb 218f
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
	vmovdqu32 ZMMWORD PTR [r11+64], zmm10
	cmp rax, 9
	jb 220f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+64]
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
	vmovdqu32 ZMMWORD PTR [r11+128], zmm10
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
	vmovdqu32 ZMMWORD PTR [r11+192], zmm10
	cmp rax, 17
	jb 222f
	vbroadcasti32x4 zmm12, XMMWORD PTR [r11+192]
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
	jmp 223f
222:
223:
	jmp 221f
220:
221:
	jmp 219f
218:
219:
	vpxord zmm2, zmm2, zmm2
	vmovdqu32 ZMMWORD PTR [r15+512], zmm2
	vmovdqu32 ZMMWORD PTR [r15+576], zmm2
	vmovdqu32 ZMMWORD PTR [r15+640], zmm2
	vmovdqu32 ZMMWORD PTR [r15+704], zmm2
	vmovdqu32 ZMMWORD PTR [r15+768], zmm2
	vmovdqu32 ZMMWORD PTR [r15+832], zmm2
	vmovdqu32 ZMMWORD PTR [r15+896], zmm2
	vmovdqu32 ZMMWORD PTR [r15+960], zmm2
	mov rdi, QWORD PTR [r15+296]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+232]
	mov rcx, QWORD PTR [r15+184]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r14
	mov r8, r15
	add r8, 1024
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
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	mov r9, QWORD PTR [r15+280]
	add r9, 4
	shr r9, 2
227:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 10
	je 228f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 230f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 231f
230:
231:
	jmp 229f
228:
229:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 227b
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 64
	jb 232f
	je 234f
	cmp rcx, 192
	jae 236f
238:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 238b
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
237:
	jmp 235f
234:
243:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 243b
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
235:
	jmp 233f
232:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
233:
	mov rdi, QWORD PTR [r15+288]
	shl rdi, 4
	add rdi, r15
	add rdi, 496
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+208]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rdx, r15
	add rdx, 384
	mov r9, QWORD PTR [r15+288]
	shr r9, 2
	mov r11, r9
	shl r11, 6
	add r11, r15
	add r11, 1344
	vpxord zmm8, zmm8, zmm8
	vpxord zmm9, zmm9, zmm9
	vpxord zmm10, zmm10, zmm10
244:
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
	add rdx, 64
	sub r11, 64
	sub r9, 1
	jne 244b
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
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 245f
	mov r10d, 0
247:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 247b
	jmp 246f
245:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
246:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 248f
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
249:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 251f
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 253f
255:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 255b
	jmp 254f
253:
254:
	test rcx, 15
	je 256f
	test rcx, 12
	je 258f
	test rcx, 8
	je 260f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	add r10, 8
	jmp 261f
260:
261:
	test rcx, 4
	je 262f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	add r10, 4
	jmp 263f
262:
263:
	test rcx, 3
	je 264f
266:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 266b
	jmp 265f
264:
265:
	jmp 259f
258:
267:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 267b
259:
	jmp 257f
256:
257:
	jmp 252f
251:
252:
	mov rax, QWORD PTR [r15+216]
	jmp 217f
216:
	cmp rbp, 12
	je 268f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 270f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 271f
270:
271:
	mov rcx, rbp
	test rcx, rcx
	je 272f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
274:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 274b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 273f
272:
273:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 269f
268:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
269:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 275f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 276f
275:
276:
	mov rcx, rbp
	test rcx, rcx
	je 277f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
279:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 279b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 278f
277:
278:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 280f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 281f
280:
281:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 282f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 283f
282:
283:
	mov rcx, rbp
	test rcx, rcx
	je 284f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
286:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 286b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 285f
284:
285:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 287f
	mov r10d, 0
289:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	jmp 288f
287:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
288:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 290f
	mov r10d, 0
292:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 292b
	jmp 291f
290:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
291:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 293f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 295f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 296f
295:
296:
	test rbp, rbp
	je 297f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
299:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 299b
	jmp 298f
297:
298:
	jmp 294f
293:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 2100f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2101f
2100:
2101:
294:
	mov rax, QWORD PTR [r15+216]
217:
	jmp 27f
26:
	mov eax, 0
27:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
21:
	ret
236:
	mov rax, rdi
	sub rax, r15
	shr rax, 4
	and rax, 3
	je 239f
	mov r8, rax
	shl r8, 4
	sub rdi, r8
	sub rsi, r8
	mov r9, rcx
	add r9, r8
	mov rcx, r8
	mov rax, -1
	shl rax, cl
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi]
	vmovdqu32 zmm6, ZMMWORD PTR [rdi]
	vporq zmm4, zmm4, zmm6
	vmovdqu32 ZMMWORD PTR [rdi], zmm4
	mov r10d, 64
	mov r8, r9
	shr r8, 6
	shl r8, 6
241:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 241b
	mov rcx, r9
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	jmp 240f
239:
242:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 242b
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
240:
	jmp 237b
20:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 2102f
	cmp rbx, 17
	jb 2104f
	jmp 2105f
2104:
	mov ecx, 1
2105:
	jmp 2103f
2102:
2103:
	test rcx, rcx
	je 2106f
	mov eax, 0
	cmp rbp, 12
	jne 2108f
	mov rcx, QWORD PTR [r15+184]
	or rcx, QWORD PTR [r15+208]
	cmp rcx, 512
	jae 2110f
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	add rcx, rdx
	cmp rcx, 32
	jae 2112f
	mov rdx, QWORD PTR [r15+208]
	mov rcx, rdx
	shl rcx, 4
	add rcx, rdx
	add rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jb 2114f
	mov eax, 1
	jmp 2115f
2114:
2115:
	jmp 2113f
2112:
2113:
	jmp 2111f
2110:
2111:
	jmp 2109f
2108:
2109:
	test rax, rax
	je 2116f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov rcx, QWORD PTR [r15+184]
	add rcx, 15
	shr rcx, 4
	mov QWORD PTR [r15+272], rcx
	mov rdx, QWORD PTR [r15+208]
	add rdx, 15
	shr rdx, 4
	mov QWORD PTR [r15+280], rdx
	mov rax, rcx
	add rax, rdx
	add rax, 1
	mov r8, rax
	add r8, 3
	shr r8, 2
	shl r8, 2
	mov QWORD PTR [r15+288], r8
	sub r8, rax
	mov QWORD PTR [r15+296], r8
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vshufi32x4 zmm0, zmm0, zmm0, 68
	vinserti128 ymm1, ymm1, xmm1, 1
	vshufi32x4 zmm1, zmm1, zmm1, 68
	vpxord zmm2, zmm2, zmm2
	vmovdqu32 ZMMWORD PTR [r15+512], zmm2
	vmovdqu32 ZMMWORD PTR [r15+576], zmm2
	vmovdqu32 ZMMWORD PTR [r15+640], zmm2
	vmovdqu32 ZMMWORD PTR [r15+704], zmm2
	vmovdqu32 ZMMWORD PTR [r15+768], zmm2
	vmovdqu32 ZMMWORD PTR [r15+832], zmm2
	vmovdqu32 ZMMWORD PTR [r15+896], zmm2
	vmovdqu32 ZMMWORD PTR [r15+960], zmm2
	mov rdi, QWORD PTR [r15+296]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+232]
	mov rcx, QWORD PTR [r15+184]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2118f
2120:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 2120b
	jmp 2119f
2118:
2119:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r14
	mov r8, r15
	add r8, 1024
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
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vpaddd ymm13, ymm14, ymm15
	vshufi32x4 zmm14, zmm14, zmm13, 68
	vpaddd ymm15, ymm15, ymm15
	vshufi32x4 zmm15, zmm15, zmm15, 68
	mov r9, QWORD PTR [r15+280]
	add r9, 4
	shr r9, 2
2121:
	vpshufb zmm3, zmm14, zmm0
	vpaddd zmm14, zmm14, zmm15
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 10
	je 2122f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm3, zmm3, zmm13
	cmp rsi, 12
	je 2124f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm3, zmm3, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm3, zmm3, zmm13
	jmp 2125f
2124:
2125:
	jmp 2123f
2122:
2123:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm3, zmm3, zmm13
	vmovdqu32 ZMMWORD PTR [rdx], zmm3
	add rdx, 64
	sub r9, 1
	jne 2121b
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 64
	jb 2126f
	je 2128f
	cmp rcx, 192
	jae 2130f
2132:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 2132b
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
2131:
	jmp 2129f
2128:
2137:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 2137b
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
2129:
	jmp 2127f
2126:
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
2127:
	mov rdi, QWORD PTR [r15+288]
	shl rdi, 4
	add rdi, r15
	add rdi, 496
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi], rax
	mov rax, QWORD PTR [r15+208]
	shl rax, 3
	bswap rax
	mov QWORD PTR [rdi+8], rax
	mov rdx, r15
	add rdx, 384
	mov r9, QWORD PTR [r15+288]
	shr r9, 2
	mov r11, r9
	shl r11, 6
	add r11, r13
	add r11, 64
	vpxord zmm8, zmm8, zmm8
	vpxord zmm9, zmm9, zmm9
	vpxord zmm10, zmm10, zmm10
2138:
	vmovdqu32 zmm12, ZMMWORD PTR [r11+128]
	vshufi32x4 zmm12, zmm12, zmm12, 78
	vmovdqu32 zmm7, ZMMWORD PTR [rdx+128]
	vpshufb zmm7, zmm7, zmm0
	vpclmulqdq zmm11, zmm7, zmm12, 0
	vpxord zmm8, zmm8, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 17
	vpxord zmm10, zmm10, zmm11
	vpclmulqdq zmm11, zmm7, zmm12, 1
	vpclmulqdq zmm7, zmm7, zmm12, 16
	vpternlogd zmm9, zmm11, zmm7, 150
	add rdx, 64
	sub r11, 64
	sub r9, 1
	jne 2138b
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
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 2139f
	mov r10d, 0
2141:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2141b
	jmp 2140f
2139:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2140:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 2142f
	mov r10d, 0
2144:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2144b
	jmp 2143f
2142:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2143:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 2145f
	mov rdi, QWORD PTR [r15+296]
	add rdi, QWORD PTR [r15+272]
	shl rdi, 4
	add rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r8, 0
	je 2147f
2149:
	vmovdqu xmm4, XMMWORD PTR [rsi+r10*1]
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+r10*1]
	vmovdqu XMMWORD PTR [rsi+r10*1], xmm4
	add r10, 16
	cmp r10, r8
	jne 2149b
	jmp 2148f
2147:
2148:
	test rcx, 15
	je 2150f
	test rcx, 12
	je 2152f
	test rcx, 8
	je 2154f
	mov rax, QWORD PTR [rsi+r10*1]
	xor rax, QWORD PTR [rdx+r10*1]
	mov QWORD PTR [rsi+r10*1], rax
	add r10, 8
	jmp 2155f
2154:
2155:
	test rcx, 4
	je 2156f
	mov eax, DWORD PTR [rsi+r10*1]
	xor eax, DWORD PTR [rdx+r10*1]
	mov DWORD PTR [rsi+r10*1], eax
	add r10, 4
	jmp 2157f
2156:
2157:
	test rcx, 3
	je 2158f
2160:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2160b
	jmp 2159f
2158:
2159:
	jmp 2153f
2152:
2161:
	movzx eax, BYTE PTR [rsi+r10*1]
	movzx r9d, BYTE PTR [rdx+r10*1]
	xor rax, r9
	mov BYTE PTR [rsi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2161b
2153:
	jmp 2151f
2150:
2151:
	jmp 2146f
2145:
2146:
	mov rax, QWORD PTR [r15+216]
	jmp 2117f
2116:
	mov eax, 0
	cmp rbp, 12
	jne 2162f
	mov rcx, QWORD PTR [r15+184]
	cmp rcx, 17
	jae 2164f
	mov rcx, QWORD PTR [r15+208]
	cmp rcx, 256
	jb 2166f
	mov eax, 1
	jmp 2167f
2166:
2167:
	jmp 2165f
2164:
2165:
	jmp 2163f
2162:
2163:
	test rax, rax
	je 2168f
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rcx, QWORD PTR [r15+184]
	test rcx, rcx
	je 2170f
	cmp rcx, 5
	je 2172f
	cmp rcx, 16
	je 2174f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, QWORD PTR [r15+232]
	mov r10d, 0
2176:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2176b
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm7, XMMWORD PTR [r15+96]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
	jmp 2175f
2174:
	mov rsi, QWORD PTR [r15+232]
	movdqu xmm7, XMMWORD PTR [rsi]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
2175:
	jmp 2173f
2172:
	mov rsi, QWORD PTR [r15+232]
	mov eax, DWORD PTR [rsi]
	movzx r10d, BYTE PTR [rsi+4]
	shl r10, 32
	add rax, r10
	movq xmm7, rax
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	pshufb xmm7, xmm0
	movdqu xmm3, XMMWORD PTR [r13+272]
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	pshufb xmm2, xmm0
	movdqu XMMWORD PTR [r14+16], xmm2
2173:
	jmp 2171f
2170:
2171:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 2177f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 2178f
2177:
2178:
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	movdqu xmm3, XMMWORD PTR [r13+272]
	movdqu xmm6, XMMWORD PTR [r13+256]
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 2179f
	pxor xmm7, xmm7
	movdqu XMMWORD PTR [r15+512], xmm7
	mov rdi, r15
	add rdi, 512
	mov rsi, QWORD PTR [r15+200]
	mov rdx, r15
	add rdx, 1040
	mov rcx, QWORD PTR [r15+208]
	mov r10d, 0
2181:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2181b
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
	jmp 2180f
2179:
	mov rax, QWORD PTR [r15+184]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+528], rax
	mov rax, QWORD PTR [r15+192]
	shl rax, 3
	bswap rax
	mov QWORD PTR [r15+536], rax
2180:
	vmovdqu xmm5, XMMWORD PTR [r14]
	vmovdqu xmm7, XMMWORD PTR [r14+48]
	vinserti128 ymm5, ymm5, xmm7, 1
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi]
	vpxord zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+16]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+32]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+48]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+64]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+80]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+96]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+112]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+128]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+144]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 10
	je 2182f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+160]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+176]
	vaesenc zmm5, zmm5, zmm13
	cmp rsi, 12
	je 2184f
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+192]
	vaesenc zmm5, zmm5, zmm13
	vbroadcasti32x4 zmm13, XMMWORD PTR [rdi+208]
	vaesenc zmm5, zmm5, zmm13
	jmp 2185f
2184:
2185:
	jmp 2183f
2182:
2183:
	vbroadcasti32x4 zmm13, XMMWORD PTR [r10]
	vaesenclast zmm5, zmm5, zmm13
	vmovdqu32 ZMMWORD PTR [r15+1024], zmm5
	vzeroupper
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+12], esi
	mov rax, QWORD PTR [r15+208]
	test rax, rax
	je 2186f
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+512]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm6, 16
	pxor xmm9, xmm11
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
	jmp 2187f
2186:
	movdqu xmm12, XMMWORD PTR [r14+16]
	pshufb xmm12, xmm0
	movdqu xmm7, XMMWORD PTR [r15+528]
	pshufb xmm7, xmm0
	pxor xmm7, xmm12
	pxor xmm8, xmm8
	pxor xmm9, xmm9
	pxor xmm10, xmm10
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 0
	pxor xmm8, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 17
	pxor xmm10, xmm11
	movdqa xmm11, xmm7
	pclmulqdq xmm11, xmm3, 1
	pxor xmm9, xmm11
	movdqa xmm11, xmm7
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
	movdqa xmm2, xmm10
	pxor xmm2, xmm8
	vpshufb xmm2, xmm2, xmm0
	vmovdqu xmm3, XMMWORD PTR [r15+1024]
	vpxor xmm2, xmm2, xmm3
	vmovdqu XMMWORD PTR [r15+112], xmm2
	vzeroupper
2187:
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 2188f
	mov r10d, 0
2190:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2190b
	jmp 2189f
2188:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2189:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 2191f
	mov r10d, 0
2193:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2193b
	jmp 2192f
2191:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2192:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 2194f
	mov rcx, QWORD PTR [r15+208]
	test rcx, rcx
	je 2196f
	mov rdi, QWORD PTR [r15+200]
	mov rsi, r15
	add rsi, 1040
	mov r10d, 0
2198:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2198b
	jmp 2197f
2196:
2197:
	jmp 2195f
2194:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 2199f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2200f
2199:
2200:
2195:
	mov rax, QWORD PTR [r15+216]
	jmp 2169f
2168:
	cmp rbp, 12
	je 2201f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2203f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2204f
2203:
2204:
	mov rcx, rbp
	test rcx, rcx
	je 2205f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2207:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2207b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2206f
2205:
2206:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2202f
2201:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
2202:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2208f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2209f
2208:
2209:
	mov rcx, rbp
	test rcx, rcx
	je 2210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2211f
2210:
2211:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 2213f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 2214f
2213:
2214:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 2215f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2216f
2215:
2216:
	mov rcx, rbp
	test rcx, rcx
	je 2217f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
2219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2219b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2218f
2217:
2218:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 2220f
	mov r10d, 0
2222:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2222b
	jmp 2221f
2220:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2221:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 2223f
	mov r10d, 0
2225:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2225b
	jmp 2224f
2223:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
2224:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 2226f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 2228f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2229f
2228:
2229:
	test rbp, rbp
	je 2230f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2232:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2232b
	jmp 2231f
2230:
2231:
	jmp 2227f
2226:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 2233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2234f
2233:
2234:
2227:
	mov rax, QWORD PTR [r15+216]
2169:
2117:
	jmp 2107f
2106:
	mov eax, 0
2107:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	jmp 21b
2130:
	mov rax, rdi
	sub rax, r15
	shr rax, 4
	and rax, 3
	je 2133f
	mov r8, rax
	shl r8, 4
	sub rdi, r8
	sub rsi, r8
	mov r9, rcx
	add r9, r8
	mov rcx, r8
	mov rax, -1
	shl rax, cl
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi]
	vmovdqu32 zmm6, ZMMWORD PTR [rdi]
	vporq zmm4, zmm4, zmm6
	vmovdqu32 ZMMWORD PTR [rdi], zmm4
	mov r10d, 64
	mov r8, r9
	shr r8, 6
	shl r8, 6
2135:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 2135b
	mov rcx, r9
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	jmp 2134f
2133:
2136:
	vmovdqu32 zmm4, ZMMWORD PTR [rsi+r10*1]
	vmovdqu32 ZMMWORD PTR [rdi+r10*1], zmm4
	add r10, 64
	cmp r10, r8
	jne 2136b
	mov eax, 1
	shl rax, cl
	sub rax, 1
	kmovq k1, rax
	vmovdqu8 zmm4 {k1}{z}, ZMMWORD PTR [rsi+r10*1]
	kmovq k1, rax
	vmovdqu8 ZMMWORD PTR [rdi+r10*1] {k1}, zmm4
2134:
	jmp 2131b
	.p2align 6

vg_aes_gcm_open_to_prepared_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_vaes_vpclmul_avx512}
	test eax, eax
	je 22f
	jmp 23f
22:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 24f
26:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	jmp 25f
24:
25:
23:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
21:
	ret
20:
	mov rax, QWORD PTR [rsp+16]
	cmp rax, 1024
	jae 27f
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rsi, QWORD PTR [rsp+96]
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	cmp rcx, 64
	jb 29f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu YMMWORD PTR [rdi], ymm0
	mov r10d, 0
	sub r10, rdi
	and r10, 31
	mov r8, rcx
	sub r8, 64
	cmp r8, r10
	jb 211f
213:
	vmovdqu ymm0, YMMWORD PTR [rsi+r10*1]
	vmovdqu ymm1, YMMWORD PTR [rsi+r10*1+32]
	vmovdqu YMMWORD PTR [rdi+r10*1], ymm0
	vmovdqu YMMWORD PTR [rdi+r10*1+32], ymm1
	add r10, 64
	cmp r8, r10
	jae 213b
	jmp 212f
211:
212:
	vmovdqu ymm0, YMMWORD PTR [rsi+rcx*1-64]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi+rcx*1-64], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 210f
29:
	cmp rcx, 32
	jb 214f
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+rcx*1-32]
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu YMMWORD PTR [rdi+rcx*1-32], ymm1
	jmp 215f
214:
	cmp rcx, 16
	jb 216f
	vmovdqu xmm0, XMMWORD PTR [rsi]
	vmovdqu xmm1, XMMWORD PTR [rsi+rcx*1-16]
	vmovdqu XMMWORD PTR [rdi], xmm0
	vmovdqu XMMWORD PTR [rdi+rcx*1-16], xmm1
	jmp 217f
216:
	cmp rcx, 8
	jb 218f
	mov rax, QWORD PTR [rsi]
	mov r8, QWORD PTR [rsi+rcx*1-8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+rcx*1-8], r8
	jmp 219f
218:
	cmp rcx, 4
	jb 220f
	mov eax, DWORD PTR [rsi]
	mov r8d, DWORD PTR [rsi+rcx*1-4]
	mov DWORD PTR [rdi], eax
	mov DWORD PTR [rdi+rcx*1-4], r8d
	jmp 221f
220:
	mov r10d, 0
	cmp r10, rcx
	je 222f
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	jmp 223f
222:
223:
221:
219:
217:
215:
210:
	vzeroupper
	mov rdi, QWORD PTR [rsp+80]
	mov rsi, QWORD PTR [rsp+72]
	mov rdx, QWORD PTR [rsp+64]
	mov rcx, QWORD PTR [rsp+56]
	mov r8, QWORD PTR [rsp+48]
	mov r9, QWORD PTR [rsp+40]
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	call {vg_aes_gcm_open_prepared_vaes_vpclmul_avx512}
	test eax, eax
	je 225f
	jmp 226f
225:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 227f
229:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 229b
	jmp 228f
227:
228:
226:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
28:
	jmp 21b
27:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_prepared_vaes_vpclmul_avx512}
	test eax, eax
	je 230f
	jmp 231f
230:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 232f
234:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
	jmp 233f
232:
233:
231:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	jmp 28b
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 223f
	jmp 224f
223:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
224:
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 225f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	jmp 230f
229:
230:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 234f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 235f
234:
235:
	test rbp, rbp
	je 236f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 246f
	jmp 247f
246:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
247:
	jmp 242f
241:
242:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 248f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 249f
248:
249:
	mov rcx, rbp
	test rcx, rcx
	je 250f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 240f
239:
240:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 271f
	jmp 272f
271:
	mov rcx, rbp
272:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
273:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 273b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 274f
	jmp 275f
274:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
275:
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 276f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	jmp 281f
280:
281:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 285f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 286f
285:
286:
	test rbp, rbp
	je 287f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
289:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 289b
	jmp 288f
287:
288:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 290f
	test rbx, rbx
	je 292f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 294f
	jmp 295f
294:
	mov rcx, rbp
295:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
296:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 296b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 297f
	jmp 298f
297:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
298:
	jmp 293f
292:
293:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 299f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 2100f
299:
2100:
	mov rcx, rbp
	test rcx, rcx
	je 2101f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 291f
290:
291:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 22f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 24f
	jmp 25f
24:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 26f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
28:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 28b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
27:
25:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 29f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 211f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 213f
	jmp 214f
213:
	mov rcx, rbp
214:
	jmp 212f
211:
	mov ecx, 0
212:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 215f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 217f
	jmp 218f
217:
	mov rcx, rbp
218:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
219:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 219b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 220f
	jmp 221f
220:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
221:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 222f
	jmp 223f
222:
	mov rcx, rbp
223:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	add r12, rcx
	sub rbp, rcx
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 225f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 210f
29:
210:
	test rbp, rbp
	je 227f
	test rbx, rbx
	je 229f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 231f
	jmp 232f
231:
	mov rcx, rbp
232:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
233:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 233b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 234f
	jmp 235f
234:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
235:
	jmp 230f
229:
230:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 236f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 237f
236:
237:
	mov rcx, rbp
	test rcx, rcx
	je 238f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
240:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 240b
	jmp 239f
238:
239:
	jmp 228f
227:
228:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 241f
	test rbx, rbx
	je 243f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 245f
	jmp 246f
245:
	mov rcx, rbp
246:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
247:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 247b
	add r12, rcx
	sub rbp, rcx
	jmp 244f
243:
244:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 248f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 249f
248:
249:
	test rbp, rbp
	je 250f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
252:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 252b
	jmp 251f
250:
251:
	jmp 242f
241:
242:
	jmp 23f
22:
23:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
21:
	ret
20:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 253f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 255f
	jmp 256f
255:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 257f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
259:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 259b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 258f
257:
258:
256:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 260f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 262f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 264f
	jmp 265f
264:
	mov rcx, rbp
265:
	jmp 263f
262:
	mov ecx, 0
263:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 266f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 268f
	jmp 269f
268:
	mov rcx, rbp
269:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
270:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 270b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 271f
	jmp 272f
271:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
272:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 273f
	jmp 274f
273:
	mov rcx, rbp
274:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
275:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 275b
	add r12, rcx
	sub rbp, rcx
	jmp 267f
266:
267:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 276f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_prepared_vaes_vpclmul_avx512}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 277f
276:
277:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 261f
260:
261:
	test rbp, rbp
	je 278f
	test rbx, rbx
	je 280f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 282f
	jmp 283f
282:
	mov rcx, rbp
283:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
284:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 284b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 285f
	jmp 286f
285:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
286:
	jmp 281f
280:
281:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 287f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 288f
287:
288:
	mov rcx, rbp
	test rcx, rcx
	je 289f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
291:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 291b
	jmp 290f
289:
290:
	jmp 279f
278:
279:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 292f
	test rbx, rbx
	je 294f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 296f
	jmp 297f
296:
	mov rcx, rbp
297:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
298:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 298b
	add r12, rcx
	sub rbp, rcx
	jmp 295f
294:
295:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 299f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	jmp 2100f
299:
2100:
	test rbp, rbp
	je 2101f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32_vaes}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
2103:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2103b
	jmp 2102f
2101:
2102:
	jmp 293f
292:
293:
	jmp 254f
253:
254:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	jmp 21b
	.p2align 6

vg_aes_gcm_seal_gather_prepared_vaes_vpclmul_avx512:
	mov rax, QWORD PTR [rdi+1024]
	cmp rax, 48
	jae 20f
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 752
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 768
	jb 24f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 26f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 27f
26:
27:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 768
	jmp 25f
24:
25:
	jb 28f
	call {vg_aes_gcm_stream_init_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 210f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 212f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_vpclmul}
	jmp 213f
212:
213:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 214f
216:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 216b
	jmp 215f
214:
215:
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_vaes_vpclmul}
	jmp 29f
28:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 217f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 218f
217:
218:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 752
	jb 219f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 221f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 222f
221:
222:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 223f
225:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 226f
228:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 228b
	jmp 227f
226:
227:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 229f
231:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 231b
	jmp 230f
229:
230:
	cmp r10, rcx
	je 232f
	cmp rcx, 16
	jb 234f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 235f
234:
236:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
235:
	jmp 233f
232:
233:
	add rdi, rcx
	sub r9, 1
	jne 225b
	jmp 224f
223:
224:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 220f
219:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 237f
239:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 240f
242:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 242b
	jmp 241f
240:
241:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 243f
245:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 245b
	jmp 244f
243:
244:
	cmp r10, rcx
	je 246f
	cmp rcx, 16
	jb 248f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 249f
248:
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
249:
	jmp 247f
246:
247:
	add rdi, rcx
	sub r9, 1
	jne 239b
	jmp 238f
237:
238:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
220:
29:
	jmp 23f
22:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 251f
253:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 254f
256:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 256b
	jmp 255f
254:
255:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 257f
259:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 259b
	jmp 258f
257:
258:
	cmp r10, rcx
	je 260f
	cmp rcx, 16
	jb 262f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 263f
262:
264:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 264b
263:
	jmp 261f
260:
261:
	add rdi, rcx
	sub r9, 1
	jne 253b
	jmp 252f
251:
252:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
23:
	lea rsp, [rsp+240]
21:
	ret
20:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov rax, QWORD PTR [rsp+32]
	cmp rax, 256
	jb 265f
	mov r11, rcx
	sub r11, 12
	cmp r9, 17
	cmovae r11, r9
	mov rax, QWORD PTR [rsp+16]
	sub rax, 1
	cmp rax, 2
	cmovae r11, rax
	jae 267f
	mov r10, QWORD PTR [rsp+8]
	mov r10, QWORD PTR [r10+8]
	mov rax, r10
	shr rax, 4
	shl rax, 4
	add rax, 16
	cmp rax, QWORD PTR [rsp+32]
	cmovae rax, r11
	or r11, rax
	mov rax, QWORD PTR [rsp+32]
	or rax, 256
	shr rax, 8
	cmp r10, 256
	cmovae rax, r11
	or r11, rax
	jmp 268f
267:
268:
	test r11, r11
	jmp 266f
265:
266:
	je 269f
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 752
	jb 271f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 768
	jb 273f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 275f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 276f
275:
276:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 768
	jmp 274f
273:
274:
	jb 277f
	call {vg_aes_gcm_stream_init_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 279f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 281f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_vpclmul}
	jmp 282f
281:
282:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 283f
285:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 285b
	jmp 284f
283:
284:
	jmp 280f
279:
280:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_vaes_vpclmul}
	jmp 278f
277:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 286f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 287f
286:
287:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 752
	jb 288f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 290f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 291f
290:
291:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 292f
294:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 295f
297:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 297b
	jmp 296f
295:
296:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 298f
2100:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2100b
	jmp 299f
298:
299:
	cmp r10, rcx
	je 2101f
	cmp rcx, 16
	jb 2103f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2104f
2103:
2105:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2105b
2104:
	jmp 2102f
2101:
2102:
	add rdi, rcx
	sub r9, 1
	jne 294b
	jmp 293f
292:
293:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 289f
288:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 2106f
2108:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2109f
2111:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2111b
	jmp 2110f
2109:
2110:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2112f
2114:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2114b
	jmp 2113f
2112:
2113:
	cmp r10, rcx
	je 2115f
	cmp rcx, 16
	jb 2117f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2118f
2117:
2119:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2119b
2118:
	jmp 2116f
2115:
2116:
	add rdi, rcx
	sub r9, 1
	jne 2108b
	jmp 2107f
2106:
2107:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
289:
278:
	jmp 272f
271:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 2120f
2122:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 2123f
2125:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 2125b
	jmp 2124f
2123:
2124:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 2126f
2128:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 2128b
	jmp 2127f
2126:
2127:
	cmp r10, rcx
	je 2129f
	cmp rcx, 16
	jb 2131f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 2132f
2131:
2133:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2133b
2132:
	jmp 2130f
2129:
2130:
	add rdi, rcx
	sub r9, 1
	jne 2122b
	jmp 2121f
2120:
2121:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
272:
	jmp 270f
269:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	cmp rax, 1
	je 2134f
	mov rcx, QWORD PTR [r10+24]
	test rcx, rcx
	je 2136f
	mov rsi, QWORD PTR [r10+16]
	mov rdi, QWORD PTR [rsp+24]
	add rdi, QWORD PTR [r10+8]
	mov r10d, 0
2138:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 2138b
	jmp 2137f
2136:
2137:
	jmp 2135f
2134:
2135:
	mov ecx, 12
	mov r10, QWORD PTR [rsp+8]
	mov rsi, QWORD PTR [r10]
	mov rdi, QWORD PTR [r10+8]
	mov rax, QWORD PTR [rsp+40]
	mov r10, QWORD PTR [rsp+32]
	mov r11, QWORD PTR [rsp+24]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_prepared_vaes_vpclmul_avx512}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
270:
	lea rsp, [rsp+240]
	jmp 21b
	.p2align 6

vg_aes_gcm_seal_prepared_vpclmul:
	lea rsp, [rsp-2600]
	mov rax, QWORD PTR [rsp+2608]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+24], rax
	mov rax, rsp
	add rax, 40
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+32]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 27f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 28f
27:
28:
	mov rcx, rbp
	test rcx, rcx
	je 29f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
211:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 211b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 210f
29:
210:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 212f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 213f
212:
213:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 214f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 215f
214:
215:
	test rbp, rbp
	je 216f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
218:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 218b
	jmp 217f
216:
217:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 219f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 220f
219:
220:
	mov rcx, rbp
	test rcx, rcx
	je 221f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
223:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 223b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 222f
221:
222:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+8], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 0
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, QWORD PTR [rsp+24]
	mov rax, QWORD PTR [r15]
	mov rdx, QWORD PTR [r15+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], rdx
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2600]
	ret
	.p2align 6

vg_aes_gcm_open_prepared_vpclmul:
	lea rsp, [rsp-2608]
	mov rax, QWORD PTR [rsp+2616]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2624]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+32], rax
	mov rax, rsp
	add rax, 48
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+40]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, r15
	add r14, 16
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+232], r8
	mov QWORD PTR [r15+184], r9
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+200], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r15+208], rax
	mov r12, rdx
	mov rbp, rcx
	mov rbx, QWORD PTR [rsp+32]
	mov QWORD PTR [r15+224], rbx
	mov ecx, 0
	cmp rbx, 4
	jb 20f
	cmp rbx, 17
	jb 22f
	jmp 23f
22:
	mov ecx, 1
23:
	jmp 21f
20:
21:
	test rcx, rcx
	je 24f
	cmp rbp, 12
	je 26f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 28f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 29f
28:
29:
	mov rcx, rbp
	test rcx, rcx
	je 210f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
212:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 212b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 211f
210:
211:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 27f
26:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
27:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov r12, QWORD PTR [r15+232]
	mov rbp, QWORD PTR [r15+184]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 213f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 214f
213:
214:
	mov rcx, rbp
	test rcx, rcx
	je 215f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r15+208]
	mov QWORD PTR [r15+192], rax
	shr rax, 4
	test rax, rax
	je 218f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	add rax, QWORD PTR [r15+200]
	mov QWORD PTR [r15+200], rax
	jmp 219f
218:
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 220f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 221f
220:
221:
	mov rcx, rbp
	test rcx, rcx
	je 222f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
224:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 224b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 223f
222:
223:
	mov rbx, QWORD PTR [r15+184]
	mov rbp, QWORD PTR [r15+192]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	mov rax, QWORD PTR [r14+16]
	mov QWORD PTR [r15+112], rax
	mov rax, QWORD PTR [r14+24]
	mov QWORD PTR [r15+120], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov rcx, r15
	add rcx, 112
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rbx, QWORD PTR [r15+224]
	mov rsi, QWORD PTR [rsp+24]
	mov eax, 0
	mov QWORD PTR [r15+256], rax
	mov QWORD PTR [r15+264], rax
	mov rdi, r15
	add rdi, 256
	mov rcx, rbx
	cmp rcx, 16
	je 225f
	mov r10d, 0
227:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 227b
	jmp 226f
225:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
226:
	mov eax, 0
	mov QWORD PTR [r15+240], rax
	mov QWORD PTR [r15+248], rax
	mov rdi, r15
	add rdi, 240
	mov rsi, r15
	add rsi, 112
	mov rcx, rbx
	cmp rcx, 16
	je 228f
	mov r10d, 0
230:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 230b
	jmp 229f
228:
	mov rax, QWORD PTR [rsi]
	mov r10, QWORD PTR [rsi+8]
	mov QWORD PTR [rdi], rax
	mov QWORD PTR [rdi+8], r10
229:
	mov rax, QWORD PTR [r15+240]
	xor rax, QWORD PTR [r15+256]
	mov rdx, QWORD PTR [r15+248]
	xor rdx, QWORD PTR [r15+264]
	or rax, rdx
	cmp rax, 1
	mov eax, 0
	adc eax, 0
	mov QWORD PTR [r15+216], rax
	test rax, rax
	je 231f
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov ebx, 0
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 233f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 234f
233:
234:
	test rbp, rbp
	je 235f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
237:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 237b
	jmp 236f
235:
236:
	jmp 232f
231:
	mov rax, QWORD PTR [r15+192]
	mov rcx, rax
	and rcx, 15
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	sub rcx, rax
	shr rax, 4
	mov r8, rax
	test rax, rax
	je 238f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 239f
238:
239:
232:
	mov rax, QWORD PTR [r15+216]
	jmp 25f
24:
	mov eax, 0
25:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2608]
	ret
	.p2align 6

vg_aes_gcm_open_to_prepared_vpclmul:
	lea rsp, [rsp-2624]
	mov rax, QWORD PTR [rsp+2632]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+2640]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+2648]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+2656]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+2664]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+2672]
	mov QWORD PTR [rsp+48], rax
	mov rax, rsp
	add rax, 64
	mov QWORD PTR [rsp+56], rax
	push rdi
	push rsi
	push rdx
	push rcx
	push r8
	push r9
	push rax
	push rax
	push rax
	push rax
	push rax
	mov rax, QWORD PTR [rsp+112]
	mov QWORD PTR [rsp], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+128]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+136]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+96]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+104]
	mov QWORD PTR [rsp+40], rax
	mov rax, QWORD PTR [rsp+144]
	mov QWORD PTR [rsp+48], rax
	call {vg_aes_gcm_open_split_vpclmul}
	test eax, eax
	je 20f
	jmp 21f
20:
	mov rdi, QWORD PTR [rsp+112]
	mov rcx, QWORD PTR [rsp+104]
	mov eax, 0
	mov r10d, 0
	cmp r10, rcx
	je 22f
24:
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 24b
	jmp 23f
22:
23:
21:
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	pop r11
	lea rsp, [rsp+2624]
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt_prepared_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 218f
	jmp 219f
218:
	mov rcx, rbp
219:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
220:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 220b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 221f
	jmp 222f
221:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
222:
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_encrypt_blocks_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	jmp 228f
227:
228:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 232f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 233f
232:
233:
	test rbp, rbp
	je 234f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
236:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 236b
	jmp 235f
234:
235:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 237f
	test rbx, rbx
	je 239f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 241f
	jmp 242f
241:
	mov rcx, rbp
242:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
243:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 243b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 244f
	jmp 245f
244:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
245:
	jmp 240f
239:
240:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 246f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 247f
246:
247:
	mov rcx, rbp
	test rcx, rcx
	je 248f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 238f
237:
238:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt_prepared_vpclmul:
	lea rsp, [rsp-2584]
	mov rax, QWORD PTR [rsp+2592]
	mov QWORD PTR [rsp+8], rax
	mov rax, rsp
	add rax, 24
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [rax+128], rbx
	mov QWORD PTR [rax+136], rbp
	mov QWORD PTR [rax+144], r12
	mov QWORD PTR [rax+152], r13
	mov QWORD PTR [rax+160], r14
	mov QWORD PTR [rax+168], r15
	mov r15, rax
	mov r14, rdx
	mov r13, rdi
	mov QWORD PTR [r15+176], rsi
	mov QWORD PTR [r15+184], rcx
	mov QWORD PTR [r15+192], r8
	mov QWORD PTR [r15+200], r9
	mov rbp, QWORD PTR [rsp+8]
	mov QWORD PTR [r15+208], rbp
	mov r12, r9
	mov rbx, r8
	and rbx, 15
	test rbp, rbp
	je 20f
	mov rax, QWORD PTR [r15+192]
	test rax, rax
	je 22f
	jmp 23f
22:
	mov rbx, QWORD PTR [r15+184]
	and rbx, 15
	test rbx, rbx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r14
	add rsi, 32
	mov rcx, rbx
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
23:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 256
	cmp rbp, rcx
	jb 27f
	mov QWORD PTR [r15+216], rbp
	test rbx, rbx
	je 29f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 211f
	jmp 212f
211:
	mov rcx, rbp
212:
	jmp 210f
29:
	mov ecx, 0
210:
	mov QWORD PTR [r15+208], rcx
	mov rbp, rcx
	test rbx, rbx
	je 213f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 215f
	jmp 216f
215:
	mov rcx, rbp
216:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
217:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 217b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 218f
	jmp 219f
218:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
219:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 220f
	jmp 221f
220:
	mov rcx, rbp
221:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
222:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 222b
	add r12, rcx
	sub rbp, rcx
	jmp 214f
213:
214:
	mov rax, QWORD PTR [r15+208]
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	mov rcx, QWORD PTR [r15+216]
	sub rcx, rax
	mov QWORD PTR [r15+208], rcx
	mov rax, QWORD PTR [r15+208]
	shr rax, 4
	test rax, rax
	je 223f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 16
	mov r8, QWORD PTR [r15+200]
	mov r9, rax
	mov rax, r15
	add rax, 448
	push rax
	call {vg_aes_gcm_decrypt_blocks_vpclmul}
	pop rax
	mov rax, QWORD PTR [r15+208]
	mov rcx, rax
	and rcx, 15
	mov QWORD PTR [r15+208], rcx
	sub rax, rcx
	mov rcx, QWORD PTR [r15+200]
	add rcx, rax
	mov QWORD PTR [r15+200], rcx
	mov rcx, QWORD PTR [r15+192]
	add rcx, rax
	mov QWORD PTR [r15+192], rcx
	jmp 224f
223:
224:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	jmp 28f
27:
28:
	test rbp, rbp
	je 225f
	test rbx, rbx
	je 227f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 229f
	jmp 230f
229:
	mov rcx, rbp
230:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
231:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 231b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 232f
	jmp 233f
232:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
233:
	jmp 228f
227:
228:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 234f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 235f
234:
235:
	mov rcx, rbp
	test rcx, rcx
	je 236f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
238:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 238b
	jmp 237f
236:
237:
	jmp 226f
225:
226:
	mov r12, QWORD PTR [r15+200]
	mov rbp, QWORD PTR [r15+208]
	mov rbx, QWORD PTR [r15+192]
	and rbx, 15
	test rbp, rbp
	je 239f
	test rbx, rbx
	je 241f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 243f
	jmp 244f
243:
	mov rcx, rbp
244:
	mov rdi, r12
	mov rsi, r14
	add rsi, rbx
	add rsi, 64
	mov r10d, 0
245:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 245b
	add r12, rcx
	sub rbp, rcx
	jmp 242f
241:
242:
	mov rcx, r12
	mov r8, rbp
	shr r8, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test r8, r8
	je 246f
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	jmp 247f
246:
247:
	test rbp, rbp
	je 248f
	mov eax, 0
	mov QWORD PTR [r14+64], rax
	mov QWORD PTR [r14+72], rax
	mov rdi, r13
	mov rsi, QWORD PTR [r15+176]
	mov rdx, r14
	add rdx, 48
	mov rcx, r14
	add rcx, 64
	mov r8d, 1
	mov r9, r15
	add r9, 512
	call {vg_aes_ctr32}
	mov rdi, r12
	mov rsi, r14
	add rsi, 64
	mov rcx, rbp
	mov r10d, 0
250:
	movzx eax, BYTE PTR [rdi+r10*1]
	movzx r11d, BYTE PTR [rsi+r10*1]
	xor rax, r11
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 250b
	jmp 249f
248:
249:
	jmp 240f
239:
240:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2584]
	ret
	.p2align 6

vg_aes_gcm_seal_gather_prepared_vpclmul:
	lea rsp, [rsp-240]
	mov rax, QWORD PTR [rsp+248]
	mov QWORD PTR [rsp+8], rax
	mov rax, QWORD PTR [rsp+256]
	mov QWORD PTR [rsp+16], rax
	mov rax, QWORD PTR [rsp+264]
	mov QWORD PTR [rsp+24], rax
	mov rax, QWORD PTR [rsp+272]
	mov QWORD PTR [rsp+32], rax
	mov rax, QWORD PTR [rsp+280]
	mov QWORD PTR [rsp+40], rax
	mov rax, rsp
	add rax, 56
	mov QWORD PTR [rsp+48], rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [rsp+8]
	mov rax, QWORD PTR [rsp+16]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], r8
	mov QWORD PTR [r11+24], r9
	mov QWORD PTR [r11+80], r9
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	mov rax, QWORD PTR [rsp+24]
	mov r10, QWORD PTR [rsp+32]
	mov r8, QWORD PTR [rsp+40]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r10
	mov QWORD PTR [r11+48], r8
	mov eax, 0
	mov QWORD PTR [r11+72], rax
	mov QWORD PTR [r11+88], rax
	mov QWORD PTR [r11+96], rax
	mov rsi, rdx
	mov rdx, rcx
	mov rcx, r11
	add rcx, 104
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483631
	jb 20f
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	cmp rax, 2147483647
	jb 22f
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 24f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 25f
24:
25:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	cmp r10, rax
	mov rax, QWORD PTR [r11+40]
	mov r10d, 0
	cmovae rax, r10
	cmp rax, 2147483647
	jmp 23f
22:
23:
	jb 26f
	call {vg_aes_gcm_stream_init_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, r11
	add rsi, 104
	mov edx, 0
	mov rcx, QWORD PTR [r11+16]
	mov r8, QWORD PTR [r11+24]
	call {vg_aes_gcm_stream_aad_vpclmul}
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+40]
	test rax, rax
	je 28f
	mov rcx, QWORD PTR [r11+24]
	mov r8, rcx
	and r8, 15
	test r8, r8
	je 210f
	mov eax, 16
	sub rax, r8
	mov r8, rax
	mov rdi, QWORD PTR [r11]
	mov rax, rcx
	add rax, r8
	mov QWORD PTR [r11+80], rax
	mov rsi, r11
	add rsi, 104
	mov rdx, rcx
	mov rcx, r11
	add rcx, 88
	call {vg_aes_gcm_stream_aad_vpclmul}
	jmp 211f
210:
211:
	mov r11, QWORD PTR [rsp+48]
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 212f
214:
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov r9, QWORD PTR [r10]
	mov rax, QWORD PTR [r10+8]
	mov r10, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+72]
	add r10, rcx
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+80]
	mov r8, QWORD PTR [r11+72]
	push rax
	push r10
	push rax
	call {vg_aes_gcm_stream_encrypt_to_vpclmul}
	pop rax
	pop rax
	pop rax
	mov r11, QWORD PTR [rsp+48]
	mov r10, QWORD PTR [r11+56]
	mov rax, QWORD PTR [r10+8]
	mov rcx, QWORD PTR [r11+72]
	add rcx, rax
	add r10, 16
	mov rax, QWORD PTR [r11+64]
	sub rax, 1
	mov QWORD PTR [r11+72], rcx
	mov QWORD PTR [r11+56], r10
	mov QWORD PTR [r11+64], rax
	test rax, rax
	jne 214b
	jmp 213f
212:
213:
	jmp 29f
28:
29:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, r11
	add rdx, 104
	mov rcx, QWORD PTR [r11+24]
	mov r8, QWORD PTR [r11+40]
	mov r9, QWORD PTR [r11+48]
	call {vg_aes_gcm_stream_finish_vpclmul}
	jmp 27f
26:
	mov r11, QWORD PTR [rsp+48]
	mov r10d, 0
	mov rax, QWORD PTR [r11+64]
	test rax, rax
	je 215f
	mov r10, QWORD PTR [r11+56]
	mov r10, QWORD PTR [r10+8]
	jmp 216f
215:
216:
	mov rax, QWORD PTR [r11+40]
	shr rax, 4
	shl rax, 4
	mov r8d, 0
	cmp r10, rax
	cmovb r10, r8
	cmp r10, 2147483631
	jb 217f
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r10, QWORD PTR [r11+56]
	mov rax, r10
	mov ecx, 0
	test r9, r9
	je 219f
	mov rax, QWORD PTR [r10]
	mov rcx, QWORD PTR [r10+8]
	sub r9, 1
	add r10, 16
	add rdi, rcx
	jmp 220f
219:
220:
	mov QWORD PTR [r11+120], rax
	mov QWORD PTR [r11+128], rcx
	mov r11, r10
	cmp r9, 0
	je 221f
223:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 224f
226:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 226b
	jmp 225f
224:
225:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 227f
229:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 229b
	jmp 228f
227:
228:
	cmp r10, rcx
	je 230f
	cmp rcx, 16
	jb 232f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 233f
232:
234:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 234b
233:
	jmp 231f
230:
231:
	add rdi, rcx
	sub r9, 1
	jne 223b
	jmp 222f
221:
222:
	mov r11, QWORD PTR [rsp+48]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov rdi, QWORD PTR [r11+128]
	mov rsi, QWORD PTR [r11+120]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	push rdi
	push rsi
	mov r11, QWORD PTR [rsp+88]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	call {vg_aes_gcm_seal_split_vpclmul}
	pop rax
	pop rax
	pop rax
	pop rax
	pop rax
	jmp 218f
217:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 235f
237:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 238f
240:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 240b
	jmp 239f
238:
239:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 241f
243:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 243b
	jmp 242f
241:
242:
	cmp r10, rcx
	je 244f
	cmp rcx, 16
	jb 246f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 247f
246:
248:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 248b
247:
	jmp 245f
244:
245:
	add rdi, rcx
	sub r9, 1
	jne 237b
	jmp 236f
235:
236:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vpclmul}
	pop rax
	pop rax
	pop rax
218:
27:
	jmp 21f
20:
	mov QWORD PTR [r11+104], rsi
	mov QWORD PTR [r11+112], rdx
	mov r9, QWORD PTR [r11+64]
	mov rdi, QWORD PTR [r11+32]
	mov r11, QWORD PTR [r11+56]
	cmp r9, 0
	je 249f
251:
	mov rsi, QWORD PTR [r11]
	mov rcx, QWORD PTR [r11+8]
	add r11, 16
	mov r10d, 0
	mov r8, rcx
	shr r8, 6
	shl r8, 6
	cmp r8, 0
	je 252f
254:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu xmm1, XMMWORD PTR [rsi+r10*1+16]
	movdqu xmm2, XMMWORD PTR [rsi+r10*1+32]
	movdqu xmm3, XMMWORD PTR [rsi+r10*1+48]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	movdqu XMMWORD PTR [rdi+r10*1+16], xmm1
	movdqu XMMWORD PTR [rdi+r10*1+32], xmm2
	movdqu XMMWORD PTR [rdi+r10*1+48], xmm3
	add r10, 64
	cmp r10, r8
	jne 254b
	jmp 253f
252:
253:
	mov r8, rcx
	shr r8, 4
	shl r8, 4
	cmp r10, r8
	je 255f
257:
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	add r10, 16
	cmp r10, r8
	jne 257b
	jmp 256f
255:
256:
	cmp r10, rcx
	je 258f
	cmp rcx, 16
	jb 260f
	mov r10, rcx
	sub r10, 16
	movdqu xmm0, XMMWORD PTR [rsi+r10*1]
	movdqu XMMWORD PTR [rdi+r10*1], xmm0
	jmp 261f
260:
262:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 262b
261:
	jmp 259f
258:
259:
	add rdi, rcx
	sub r9, 1
	jne 251b
	jmp 250f
249:
250:
	mov r11, QWORD PTR [rsp+48]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+104]
	mov rcx, QWORD PTR [r11+112]
	mov r8, QWORD PTR [r11+16]
	mov r9, QWORD PTR [r11+24]
	mov rax, QWORD PTR [r11+48]
	mov r10, QWORD PTR [r11+40]
	mov r11, QWORD PTR [r11+32]
	push rax
	push r10
	push r11
	call {vg_aes_gcm_seal_vpclmul}
	pop rax
	pop rax
	pop rax
21:
	lea rsp, [rsp+240]
	ret
	.p2align 6

vg_aes_gcm_stream_init_pclmul:
	lea rsp, [rsp-2568]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov r14, rcx
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_stream_aad_pclmul:
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 20f
	test rbx, rbx
	je 22f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 24f
	jmp 25f
24:
	mov rcx, rbp
25:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 27f
	jmp 28f
27:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
28:
	jmp 23f
22:
23:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_pclmul}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_stream_init:
	lea rsp, [rsp-2568]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov r14, rcx
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_stream_aad:
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 20f
	test rbx, rbx
	je 22f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 24f
	jmp 25f
24:
	mov rcx, rbp
25:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 27f
	jmp 28f
27:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash}
28:
	jmp 23f
22:
23:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_stream_init_vpclmul:
	lea rsp, [rsp-2568]
	mov r8, rsp
	add r8, 8
	mov QWORD PTR [r8+128], rbx
	mov QWORD PTR [r8+136], rbp
	mov QWORD PTR [r8+144], r12
	mov QWORD PTR [r8+152], r13
	mov QWORD PTR [r8+160], r14
	mov QWORD PTR [r8+168], r15
	mov r15, r8
	mov r14, rcx
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	cmp rbp, 12
	je 20f
	mov eax, 0
	mov QWORD PTR [r14], rax
	mov QWORD PTR [r14+8], rax
	mov QWORD PTR [r15+216], rbp
	mov ebx, 0
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 22f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 23f
22:
23:
	mov rcx, rbp
	test rcx, rcx
	je 24f
	mov eax, 0
	mov QWORD PTR [r15+96], rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r15
	add rdi, 96
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 25f
24:
25:
	mov ebx, 0
	mov rbp, QWORD PTR [r15+216]
	mov rax, rbx
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+96], rax
	mov rax, rbp
	add rax, rax
	add rax, rax
	add rax, rax
	bswap rax
	mov QWORD PTR [r15+104], rax
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 0
	mov rdx, r15
	add rdx, 96
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 21f
20:
	mov eax, DWORD PTR [r12]
	mov ecx, DWORD PTR [r12+4]
	mov edx, DWORD PTR [r12+8]
	mov esi, 16777216
	mov DWORD PTR [r14], eax
	mov DWORD PTR [r14+4], ecx
	mov DWORD PTR [r14+8], edx
	mov DWORD PTR [r14+12], esi
21:
	mov eax, DWORD PTR [r14]
	mov ecx, DWORD PTR [r14+4]
	mov edx, DWORD PTR [r14+8]
	mov esi, DWORD PTR [r14+12]
	bswap esi
	add esi, 1
	bswap esi
	mov DWORD PTR [r14+48], eax
	mov DWORD PTR [r14+52], ecx
	mov DWORD PTR [r14+56], edx
	mov DWORD PTR [r14+60], esi
	mov eax, 0
	mov QWORD PTR [r14+16], rax
	mov QWORD PTR [r14+24], rax
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6

vg_aes_gcm_stream_aad_vpclmul:
	lea rsp, [rsp-2568]
	mov r9, rsp
	add r9, 8
	mov QWORD PTR [r9+128], rbx
	mov QWORD PTR [r9+136], rbp
	mov QWORD PTR [r9+144], r12
	mov QWORD PTR [r9+152], r13
	mov QWORD PTR [r9+160], r14
	mov QWORD PTR [r9+168], r15
	mov r15, r9
	mov r14, rsi
	mov r13, rdi
	mov r12, rcx
	mov rbp, r8
	mov rbx, rdx
	and rbx, 15
	test rbp, rbp
	je 20f
	test rbx, rbx
	je 22f
	mov ecx, 16
	sub rcx, rbx
	cmp rbp, rcx
	jb 24f
	jmp 25f
24:
	mov rcx, rbp
25:
	mov rdi, r14
	add rdi, rbx
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
26:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 26b
	add r12, rcx
	sub rbp, rcx
	add rbx, rcx
	cmp rbx, 16
	je 27f
	jmp 28f
27:
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov rdx, r14
	add rdx, 32
	mov ecx, 1
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
28:
	jmp 23f
22:
23:
	mov rdx, r12
	mov rcx, rbp
	shr rcx, 4
	mov rax, rbp
	and rbp, 15
	sub rax, rbp
	add r12, rax
	test rcx, rcx
	je 29f
	mov rdi, r13
	add rdi, 240
	mov rsi, r14
	add rsi, 16
	mov r8, r15
	add r8, 512
	call {vg_ghash_vpclmul}
	jmp 210f
29:
210:
	mov rcx, rbp
	test rcx, rcx
	je 211f
	mov rdi, r14
	add rdi, 32
	mov rsi, r12
	mov r10d, 0
213:
	movzx eax, BYTE PTR [rsi+r10*1]
	mov BYTE PTR [rdi+r10*1], al
	add r10, 1
	cmp r10, rcx
	jne 213b
	jmp 212f
211:
212:
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+128]
	mov rbp, QWORD PTR [r15+136]
	mov r12, QWORD PTR [r15+144]
	mov r13, QWORD PTR [r15+152]
	mov r14, QWORD PTR [r15+160]
	mov r15, QWORD PTR [r15+168]
	lea rsp, [rsp+2568]
	ret
	.p2align 6
