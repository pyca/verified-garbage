// The functions of `src/internal/vg_aes_gcm_decrypt_blocks_prepared16_vaes_vpclmul.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_decrypt_blocks_prepared16_vaes_vpclmul:
	mov r11, QWORD PTR [rsp+8]
	mov QWORD PTR [r11], rdi
	mov QWORD PTR [r11+8], rsi
	mov QWORD PTR [r11+16], rdx
	mov QWORD PTR [r11+24], rcx
	mov QWORD PTR [r11+32], r8
	mov QWORD PTR [r11+40], r9
	cmp r9, 16
	jb 20f
	add r11, 127
	and r11, -64
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vmovdqu ymm4, YMMWORD PTR [rdi+448]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vmovdqu ymm6, YMMWORD PTR [rdi+384]
	vmovdqu ymm15, YMMWORD PTR [rdi+352]
	vmovdqu ymm14, YMMWORD PTR [rdi+320]
	vmovdqu ymm13, YMMWORD PTR [rdi+288]
	vmovdqu ymm12, YMMWORD PTR [rdi+256]
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
	cmp r9, 16
	jb 22f
24:
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
	je 25f
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
	je 27f
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
	jmp 28f
27:
28:
	jmp 26f
25:
26:
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
	je 29f
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
	je 211f
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
	jmp 212f
211:
212:
	jmp 210f
29:
210:
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
	jae 24b
	test r9, r9
	je 213f
	add r9, 16
	mov r10, r9
	sub r10, 16
	vmovq xmm13, r10
	vpaddd xmm13, xmm14, xmm13
	vpshufb xmm13, xmm13, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	mov rax, r11
	add rax, 256
	sub rax, r10
	cmp r10, 129
	jb 215f
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 217f
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
	je 219f
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
	jmp 220f
219:
220:
	jmp 218f
217:
218:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 221f
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
	je 223f
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
	jmp 224f
223:
224:
	jmp 222f
221:
222:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+384], ymm3
	vmovdqu YMMWORD PTR [r11+416], ymm4
	vmovdqu YMMWORD PTR [r11+448], ymm5
	vmovdqu YMMWORD PTR [r11+480], ymm6
	jmp 216f
215:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 225f
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
	je 227f
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
	jmp 228f
227:
228:
	jmp 226f
225:
226:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
216:
	sub r11, 512
	mov r10d, 0
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	test r9, 1
	je 229f
	vmovdqu xmm13, XMMWORD PTR [rdx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm12, xmm12, xmm13
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm12
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jmp 230f
229:
	cmp r9, 16
230:
	je 231f
233:
	vmovdqu ymm13, YMMWORD PTR [rdx+r10*1]
	vmovdqu ymm12, YMMWORD PTR [r11+r10*1+768]
	vpxor ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rdx+r10*1], ymm12
	vmovdqu ymm12, YMMWORD PTR [rax+r10*1]
	vpshufb ymm13, ymm13, ymm0
	vpxor ymm13, ymm13, ymm2
	vpxor ymm2, ymm2, ymm2
	vpclmulqdq ymm11, ymm13, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	add r10, 32
	sub r9, 2
	cmp r9, 16
	jne 233b
	vextracti128 xmm11, ymm8, 1
	vpxor xmm8, xmm8, xmm11
	vextracti128 xmm11, ymm9, 1
	vpxor xmm9, xmm9, xmm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm10, xmm10, xmm11
	jmp 232f
231:
232:
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	add r11, 512
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	jmp 214f
213:
	vpshufb xmm13, xmm14, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
214:
	jmp 23f
22:
	add r9, 16
	mov r10, r9
	sub r10, 16
	vmovq xmm13, r10
	vpaddd xmm13, xmm14, xmm13
	vpshufb xmm13, xmm13, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	mov rax, r11
	add rax, 256
	sub rax, r10
	cmp r10, 129
	jb 234f
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 236f
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
	je 238f
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
	jmp 239f
238:
239:
	jmp 237f
236:
237:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 240f
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
	je 242f
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
	jmp 243f
242:
243:
	jmp 241f
240:
241:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+384], ymm3
	vmovdqu YMMWORD PTR [r11+416], ymm4
	vmovdqu YMMWORD PTR [r11+448], ymm5
	vmovdqu YMMWORD PTR [r11+480], ymm6
	jmp 235f
234:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 244f
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
	je 246f
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
	jmp 247f
246:
247:
	jmp 245f
244:
245:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
235:
	sub r11, 512
	mov r10d, 0
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	test r9, 1
	je 248f
	vmovdqu xmm13, XMMWORD PTR [rdx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm12, xmm12, xmm13
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm12
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jmp 249f
248:
	cmp r9, 16
249:
	je 250f
252:
	vmovdqu ymm13, YMMWORD PTR [rdx+r10*1]
	vmovdqu ymm12, YMMWORD PTR [r11+r10*1+768]
	vpxor ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rdx+r10*1], ymm12
	vmovdqu ymm12, YMMWORD PTR [rax+r10*1]
	vpshufb ymm13, ymm13, ymm0
	vpxor ymm13, ymm13, ymm2
	vpxor ymm2, ymm2, ymm2
	vpclmulqdq ymm11, ymm13, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	add r10, 32
	sub r9, 2
	cmp r9, 16
	jne 252b
	vextracti128 xmm11, ymm8, 1
	vpxor xmm8, xmm8, xmm11
	vextracti128 xmm11, ymm9, 1
	vpxor xmm9, xmm9, xmm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm10, xmm10, xmm11
	jmp 251f
250:
251:
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	add r11, 512
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
23:
	jmp 21f
20:
	cmp r9, 2
	jb 253f
	add r11, 127
	and r11, -64
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm0, XMMWORD PTR [rax]
	lea rax, {VG_GCM_CONSTS}
	movdqu xmm1, XMMWORD PTR [rax+16]
	vinserti128 ymm0, ymm0, xmm0, 1
	vinserti128 ymm1, ymm1, xmm1, 1
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vmovdqu ymm4, YMMWORD PTR [rdi+448]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vmovdqu ymm6, YMMWORD PTR [rdi+384]
	vmovdqu ymm15, YMMWORD PTR [rdi+352]
	vmovdqu ymm14, YMMWORD PTR [rdi+320]
	vmovdqu ymm13, YMMWORD PTR [rdi+288]
	vmovdqu ymm12, YMMWORD PTR [rdi+256]
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
	cmp r9, 16
	jb 255f
257:
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
	je 258f
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
	je 260f
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
	jmp 261f
260:
261:
	jmp 259f
258:
259:
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
	je 262f
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
	je 264f
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
	jmp 265f
264:
265:
	jmp 263f
262:
263:
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
	jae 257b
	test r9, r9
	je 266f
	add r9, 16
	mov r10, r9
	sub r10, 16
	vmovq xmm13, r10
	vpaddd xmm13, xmm14, xmm13
	vpshufb xmm13, xmm13, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	mov rax, r11
	add rax, 256
	sub rax, r10
	cmp r10, 129
	jb 268f
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 270f
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
	je 272f
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
	jmp 273f
272:
273:
	jmp 271f
270:
271:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 274f
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
	je 276f
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
	jmp 277f
276:
277:
	jmp 275f
274:
275:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+384], ymm3
	vmovdqu YMMWORD PTR [r11+416], ymm4
	vmovdqu YMMWORD PTR [r11+448], ymm5
	vmovdqu YMMWORD PTR [r11+480], ymm6
	jmp 269f
268:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 278f
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
	je 280f
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
	jmp 281f
280:
281:
	jmp 279f
278:
279:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
269:
	sub r11, 512
	mov r10d, 0
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	test r9, 1
	je 282f
	vmovdqu xmm13, XMMWORD PTR [rdx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm12, xmm12, xmm13
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm12
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jmp 283f
282:
	cmp r9, 16
283:
	je 284f
286:
	vmovdqu ymm13, YMMWORD PTR [rdx+r10*1]
	vmovdqu ymm12, YMMWORD PTR [r11+r10*1+768]
	vpxor ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rdx+r10*1], ymm12
	vmovdqu ymm12, YMMWORD PTR [rax+r10*1]
	vpshufb ymm13, ymm13, ymm0
	vpxor ymm13, ymm13, ymm2
	vpxor ymm2, ymm2, ymm2
	vpclmulqdq ymm11, ymm13, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	add r10, 32
	sub r9, 2
	cmp r9, 16
	jne 286b
	vextracti128 xmm11, ymm8, 1
	vpxor xmm8, xmm8, xmm11
	vextracti128 xmm11, ymm9, 1
	vpxor xmm9, xmm9, xmm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm10, xmm10, xmm11
	jmp 285f
284:
285:
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	add r11, 512
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
	jmp 267f
266:
	vpshufb xmm13, xmm14, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
267:
	jmp 256f
255:
	add r9, 16
	mov r10, r9
	sub r10, 16
	vmovq xmm13, r10
	vpaddd xmm13, xmm14, xmm13
	vpshufb xmm13, xmm13, xmm0
	vmovdqu XMMWORD PTR [rax], xmm13
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	mov rax, r11
	add rax, 256
	sub rax, r10
	cmp r10, 129
	jb 287f
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 289f
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
	je 291f
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
	jmp 292f
291:
292:
	jmp 290f
289:
290:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 293f
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
	je 295f
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
	jmp 296f
295:
296:
	jmp 294f
293:
294:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+384], ymm3
	vmovdqu YMMWORD PTR [r11+416], ymm4
	vmovdqu YMMWORD PTR [r11+448], ymm5
	vmovdqu YMMWORD PTR [r11+480], ymm6
	jmp 288f
287:
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
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
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+32]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+48]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
	vbroadcasti128 ymm13, XMMWORD PTR [rdi+64]
	vaesenc ymm3, ymm3, ymm13
	vaesenc ymm4, ymm4, ymm13
	vaesenc ymm5, ymm5, ymm13
	vaesenc ymm6, ymm6, ymm13
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
	je 297f
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
	je 299f
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
	jmp 2100f
299:
2100:
	jmp 298f
297:
298:
	vbroadcasti128 ymm13, XMMWORD PTR [r10]
	vaesenclast ymm3, ymm3, ymm13
	vaesenclast ymm4, ymm4, ymm13
	vaesenclast ymm5, ymm5, ymm13
	vaesenclast ymm6, ymm6, ymm13
	vmovdqu YMMWORD PTR [r11+256], ymm3
	vmovdqu YMMWORD PTR [r11+288], ymm4
	vmovdqu YMMWORD PTR [r11+320], ymm5
	vmovdqu YMMWORD PTR [r11+352], ymm6
288:
	sub r11, 512
	mov r10d, 0
	vpxor xmm8, xmm8, xmm8
	vpxor xmm9, xmm9, xmm9
	vpxor xmm10, xmm10, xmm10
	test r9, 1
	je 2101f
	vmovdqu xmm13, XMMWORD PTR [rdx+r10*1]
	vmovdqu xmm12, XMMWORD PTR [r11+r10*1+768]
	vpxor xmm12, xmm12, xmm13
	vmovdqu XMMWORD PTR [rdx+r10*1], xmm12
	vpshufb xmm13, xmm13, xmm0
	vpxor xmm13, xmm13, xmm2
	vpxor xmm2, xmm2, xmm2
	vmovdqu xmm12, XMMWORD PTR [rax+r10*1]
	vpclmulqdq xmm11, xmm13, xmm12, 0
	vpxor xmm8, xmm8, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 17
	vpxor xmm10, xmm10, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 1
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm13, xmm12, 16
	vpxor xmm9, xmm9, xmm11
	add r10, 16
	sub r9, 1
	cmp r9, 16
	jmp 2102f
2101:
	cmp r9, 16
2102:
	je 2103f
2105:
	vmovdqu ymm13, YMMWORD PTR [rdx+r10*1]
	vmovdqu ymm12, YMMWORD PTR [r11+r10*1+768]
	vpxor ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [rdx+r10*1], ymm12
	vmovdqu ymm12, YMMWORD PTR [rax+r10*1]
	vpshufb ymm13, ymm13, ymm0
	vpxor ymm13, ymm13, ymm2
	vpxor ymm2, ymm2, ymm2
	vpclmulqdq ymm11, ymm13, ymm12, 0
	vpxor ymm8, ymm8, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 17
	vpxor ymm10, ymm10, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 1
	vpxor ymm9, ymm9, ymm11
	vpclmulqdq ymm11, ymm13, ymm12, 16
	vpxor ymm9, ymm9, ymm11
	add r10, 32
	sub r9, 2
	cmp r9, 16
	jne 2105b
	vextracti128 xmm11, ymm8, 1
	vpxor xmm8, xmm8, xmm11
	vextracti128 xmm11, ymm9, 1
	vpxor xmm9, xmm9, xmm11
	vextracti128 xmm11, ymm10, 1
	vpxor xmm10, xmm10, xmm11
	jmp 2104f
2103:
2104:
	vpclmulqdq xmm11, xmm8, xmm1, 16
	vpshufd xmm8, xmm8, 78
	vpxor xmm9, xmm9, xmm8
	vpxor xmm9, xmm9, xmm11
	vpclmulqdq xmm11, xmm9, xmm1, 16
	vpshufd xmm9, xmm9, 78
	vpxor xmm2, xmm10, xmm9
	vpxor xmm2, xmm2, xmm11
	add r11, 512
	vpshufb xmm2, xmm2, xmm0
	vmovdqu XMMWORD PTR [rcx], xmm2
	vzeroupper
256:
	jmp 254f
253:
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
	je 2106f
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
	jmp 2107f
2106:
2107:
254:
21:
	ret
	.p2align 6
