// The functions of `src/internal/vg_aes_gcm_decrypt_blocks_vaes_vpclmul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_decrypt_blocks_vaes_vpclmul:
	mov r11, QWORD PTR [rsp+8]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
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
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
22:
	vpxor ymm8, ymm8, ymm8
	vpxor ymm9, ymm9, ymm9
	vpxor ymm10, ymm10, ymm10
	vpshufb ymm3, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vpshufb ymm4, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vpshufb ymm5, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vpshufb ymm6, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+32]
	vmovdqu ymm7, YMMWORD PTR [rdx+32]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+64]
	vmovdqu ymm7, YMMWORD PTR [rdx+64]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+96]
	vmovdqu ymm7, YMMWORD PTR [rdx+96]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11]
	vmovdqu ymm7, YMMWORD PTR [rdx]
	vpshufb ymm7, ymm7, ymm0
	vpxor ymm7, ymm7, ymm2
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 23f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 25f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 26f
25:
26:
	jmp 24f
23:
24:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+32]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+32], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+64]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+64], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+96]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+96], ymm6
	vpshufb ymm3, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vpshufb ymm4, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vpshufb ymm5, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vpshufb ymm6, ymm14, ymm0
	vpaddd ymm14, ymm14, ymm15
	vbroadcasti128 ymm13, XMMWORD PTR [rdi]
	vpxor ymm3, ymm3, ymm13
	vpxor ymm4, ymm4, ymm13
	vpxor ymm5, ymm5, ymm13
	vpxor ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+16]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+128]
	vmovdqu ymm7, YMMWORD PTR [rdx+128]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+160]
	vmovdqu ymm7, YMMWORD PTR [rdx+160]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+192]
	vmovdqu ymm7, YMMWORD PTR [rdx+192]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vmovdqu ymm12, YMMWORD PTR [r11+224]
	vmovdqu ymm7, YMMWORD PTR [rdx+224]
	vpshufb ymm7, ymm7, ymm0
	vpclmulqdq ymm11, ymm7, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm7, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+80]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	vpxor ymm7, ymm10, ymm8
	vextracti128 xmm11, ymm7, 1
	vpxor xmm2, xmm7, xmm11
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+96]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+112]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+128]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+144]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 10
	je 27f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+160]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+176]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	cmp rsi, 12
	je 29f
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+192]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+208]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	jmp 210f
29:
210:
	jmp 28f
27:
28:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu ymm13, YMMWORD PTR [rdx+128]
	vpxor ymm3, ymm3, ymm13
	vmovdqu YMMWORD PTR [rdx+128], ymm3
	vmovdqu ymm13, YMMWORD PTR [rdx+160]
	vpxor ymm4, ymm4, ymm13
	vmovdqu YMMWORD PTR [rdx+160], ymm4
	vmovdqu ymm13, YMMWORD PTR [rdx+192]
	vpxor ymm5, ymm5, ymm13
	vmovdqu YMMWORD PTR [rdx+192], ymm5
	vmovdqu ymm13, YMMWORD PTR [rdx+224]
	vpxor ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [rdx+224], ymm6
	add rdx, 256
	sub r9, 16
	cmp r9, 16
	jae 22b
	vpshufb xmm13, xmm14, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	jmp 21f
20:
21:
	mov r11, QWORD PTR [rsp+8]
	mov r8, QWORD PTR [r11+40]
	mov rax, r8
	and r8, 15
	sub rax, r8
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [r11+32]
	mov QWORD PTR [r11+32], rax
	mov QWORD PTR [r11+40], r8
	mov r11, QWORD PTR [rsp+8]
	mov r8, QWORD PTR [r11+40]
	test r8, r8
	je 211f
	mov r11, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [r11]
	add rdi, 240
	mov rsi, QWORD PTR [r11+24]
	mov rdx, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+40]
	mov r8, r11
	add r8, 64
	call {vg_ghash_vpclmul}
	mov r11, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+32]
	mov r8, QWORD PTR [r11+40]
	mov r9, r11
	add r9, 64
	call {vg_aes_ctr32_vaes}
	jmp 212f
211:
212:
	ret
	.p2align 6
