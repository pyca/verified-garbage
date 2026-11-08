// The functions of `src/internal/vg_aes_gcm_decrypt_blocks_aesni_pclmul_avx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_decrypt_blocks_aesni_pclmul_avx:
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
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm3, xmm3, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm3, xmm3, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm3, xmm3, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm3, xmm3, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm4, xmm10, xmm8
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm4, xmm3, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm4, xmm3, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm4, xmm3, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm4, xmm3, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm5, xmm10, xmm8
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm4, xmm4, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm4, xmm4, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm4, xmm4, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm4, xmm4, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm6, xmm10, xmm8
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm6, xmm3, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm6, xmm3, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm6, xmm3, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm6, xmm3, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm12, xmm10, xmm8
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm6, xmm4, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm6, xmm4, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm6, xmm4, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm6, xmm4, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm13, xmm10, xmm8
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm6, xmm5, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm6, xmm5, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm6, xmm5, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm6, xmm5, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm14, xmm10, xmm8
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	vpclmulqdq xmm11, xmm6, xmm6, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm6, xmm6, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm6, xmm6, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm6, xmm6, 16
	vpxor xmm9, xmm9, xmm11
	vpsrldq xmm11, xmm9, 8
	vpxor xmm10, xmm10, xmm11
	vpslldq xmm9, xmm9, 8
	vpxor xmm8, xmm8, xmm9
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm8, xmm8, xmm11
	vpxor xmm15, xmm10, xmm8
	vmovdqu XMMWORD PTR [r11+240], xmm3
	vmovdqu XMMWORD PTR [r11+224], xmm4
	vmovdqu XMMWORD PTR [r11+208], xmm5
	vmovdqu XMMWORD PTR [r11+192], xmm6
	vmovdqu XMMWORD PTR [r11+176], xmm12
	vmovdqu XMMWORD PTR [r11+160], xmm13
	vmovdqu XMMWORD PTR [r11+144], xmm14
	vmovdqu XMMWORD PTR [r11+128], xmm15
	vmovdqu xmm2, XMMWORD PTR [rcx]
	vpshufb xmm2, xmm2, xmm0
	mov r10, rsi
	shl r10, 4
	add r10, rdi
	mov rax, rdx
	mov rdx, r8
	vmovdqu XMMWORD PTR [r11+768], xmm0
	vmovdqu XMMWORD PTR [r11+784], xmm1
	mov QWORD PTR [r11+808], rdx
	mov QWORD PTR [r11+800], rsi
	mov rsi, rax
	vmovdqu xmm7, XMMWORD PTR [rax]
	mov r8d, DWORD PTR [rax+12]
	bswap r8d
	vmovdqu XMMWORD PTR [r11+640], xmm7
	vmovdqu XMMWORD PTR [r11+656], xmm7
	vmovdqu XMMWORD PTR [r11+672], xmm7
	vmovdqu XMMWORD PTR [r11+688], xmm7
	vmovdqu XMMWORD PTR [r11+704], xmm7
	vmovdqu XMMWORD PTR [r11+720], xmm7
	vmovdqu XMMWORD PTR [r11+736], xmm7
	vmovdqu XMMWORD PTR [r11+752], xmm7
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	add r8d, 8
	mov rax, rdi
	add rax, 160
	cmp r10, rax
	je 22f
	add rax, 32
	cmp r10, rax
	je 24f
26:
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	add rdx, 128
	sub r9, 8
	cmp r9, 16
	jae 26b
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+192]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+208]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	mov rax, rsi
	sub r8d, 8
	bswap r8d
	mov DWORD PTR [rax+12], r8d
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r8, QWORD PTR [r11+808]
	mov rsi, QWORD PTR [r11+800]
	jmp 25f
24:
27:
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	add rdx, 128
	sub r9, 8
	cmp r9, 16
	jae 27b
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+160]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+176]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	mov rax, rsi
	sub r8d, 8
	bswap r8d
	mov DWORD PTR [rax+12], r8d
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r8, QWORD PTR [r11+808]
	mov rsi, QWORD PTR [r11+800]
25:
	jmp 23f
22:
28:
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	add rdx, 128
	sub r9, 8
	cmp r9, 16
	jae 28b
	vmovdqu xmm0, XMMWORD PTR [r11+640]
	vmovdqu xmm3, XMMWORD PTR [r11+656]
	vmovdqu xmm4, XMMWORD PTR [r11+672]
	vmovdqu xmm5, XMMWORD PTR [r11+688]
	vmovdqu xmm6, XMMWORD PTR [r11+704]
	vmovdqu xmm13, XMMWORD PTR [r11+720]
	vmovdqu xmm14, XMMWORD PTR [r11+736]
	vmovdqu xmm15, XMMWORD PTR [r11+752]
	vmovdqu xmm1, XMMWORD PTR [rdi]
	vpxor xmm0, xmm0, xmm1
	vpxor xmm3, xmm3, xmm1
	vpxor xmm4, xmm4, xmm1
	vpxor xmm5, xmm5, xmm1
	vpxor xmm6, xmm6, xmm1
	vpxor xmm13, xmm13, xmm1
	vpxor xmm14, xmm14, xmm1
	vpxor xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [rdi+16]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+144]
	vmovdqu xmm7, XMMWORD PTR [rdx+16]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm8, xmm7, xmm12, 0
	vpclmulqdq xmm10, xmm7, xmm12, 17
	vpclmulqdq xmm9, xmm7, xmm12, 1
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 0
	bswap eax
	mov DWORD PTR [r11+652], eax
	mov eax, r8d
	add eax, 1
	bswap eax
	mov DWORD PTR [r11+668], eax
	mov eax, r8d
	add eax, 2
	bswap eax
	mov DWORD PTR [r11+684], eax
	mov eax, r8d
	add eax, 3
	bswap eax
	mov DWORD PTR [r11+700], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+32]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+160]
	vmovdqu xmm7, XMMWORD PTR [rdx+32]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	mov eax, r8d
	add eax, 4
	bswap eax
	mov DWORD PTR [r11+716], eax
	mov eax, r8d
	add eax, 5
	bswap eax
	mov DWORD PTR [r11+732], eax
	mov eax, r8d
	add eax, 6
	bswap eax
	mov DWORD PTR [r11+748], eax
	mov eax, r8d
	add eax, 7
	bswap eax
	mov DWORD PTR [r11+764], eax
	vmovdqu xmm1, XMMWORD PTR [rdi+48]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+176]
	vmovdqu xmm7, XMMWORD PTR [rdx+48]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+64]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+192]
	vmovdqu xmm7, XMMWORD PTR [rdx+64]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+80]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+208]
	vmovdqu xmm7, XMMWORD PTR [rdx+80]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+96]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+224]
	vmovdqu xmm7, XMMWORD PTR [rdx+96]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+112]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+240]
	vmovdqu xmm7, XMMWORD PTR [rdx+112]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+128]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm12, XMMWORD PTR [r11+128]
	vmovdqu xmm7, XMMWORD PTR [rdx]
	vpshufb xmm7, xmm7, XMMWORD PTR [r11+768]
	vpxor xmm7, xmm7, xmm2
	vpclmulqdq xmm11, xmm7, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm7, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	vmovdqu xmm1, XMMWORD PTR [rdi+144]
	vaesenc xmm0, xmm0, xmm1
	vaesenc xmm3, xmm3, xmm1
	vaesenc xmm4, xmm4, xmm1
	vaesenc xmm5, xmm5, xmm1
	vaesenc xmm6, xmm6, xmm1
	vaesenc xmm13, xmm13, xmm1
	vaesenc xmm14, xmm14, xmm1
	vaesenc xmm15, xmm15, xmm1
	vmovdqu xmm1, XMMWORD PTR [r11+784]
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	vmovdqu xmm1, XMMWORD PTR [r10]
	vaesenclast xmm0, xmm0, xmm1
	vaesenclast xmm3, xmm3, xmm1
	vaesenclast xmm4, xmm4, xmm1
	vaesenclast xmm5, xmm5, xmm1
	vaesenclast xmm6, xmm6, xmm1
	vaesenclast xmm13, xmm13, xmm1
	vaesenclast xmm14, xmm14, xmm1
	vaesenclast xmm15, xmm15, xmm1
	vpxor xmm0, xmm0, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdx], xmm0
	vpxor xmm3, xmm3, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdx+16], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdx+32], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdx+48], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rdx+64]
	vmovdqu XMMWORD PTR [rdx+64], xmm6
	vpxor xmm13, xmm13, XMMWORD PTR [rdx+80]
	vmovdqu XMMWORD PTR [rdx+80], xmm13
	vpxor xmm14, xmm14, XMMWORD PTR [rdx+96]
	vmovdqu XMMWORD PTR [rdx+96], xmm14
	vpxor xmm15, xmm15, XMMWORD PTR [rdx+112]
	vmovdqu XMMWORD PTR [rdx+112], xmm15
	add r8d, 8
	mov rax, rsi
	sub r8d, 8
	bswap r8d
	mov DWORD PTR [rax+12], r8d
	vmovdqu xmm0, XMMWORD PTR [r11+768]
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	mov r8, QWORD PTR [r11+808]
	mov rsi, QWORD PTR [r11+800]
23:
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
	je 29f
	mov r11, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [r11]
	add rdi, 240
	mov rsi, QWORD PTR [r11+24]
	mov rdx, QWORD PTR [r11+32]
	mov rcx, QWORD PTR [r11+40]
	mov r8, r11
	add r8, 64
	call {vg_ghash_pclmul}
	mov r11, QWORD PTR [rsp+8]
	mov rdi, QWORD PTR [r11]
	mov rsi, QWORD PTR [r11+8]
	mov rdx, QWORD PTR [r11+16]
	mov rcx, QWORD PTR [r11+32]
	mov r8, QWORD PTR [r11+40]
	mov r9, r11
	add r9, 64
	call {vg_aes_ctr32_aesni}
	jmp 210f
29:
210:
	ret
	.p2align 6
