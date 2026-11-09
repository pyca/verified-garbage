// The functions of `src/internal/vg_aes_xts_encrypt_vaes_vpclmul_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_vaes_vpclmul_avx512:
	test r8, r8
	je 20f
	mov r11, rcx
	mov rax, r8
	mov r8, r9
	mov r9, rax
	mov rax, QWORD PTR [rdx]
	mov rcx, QWORD PTR [rdx+8]
	mov QWORD PTR [r8+256], rax
	mov QWORD PTR [r8+264], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+272], rax
	mov QWORD PTR [r8+280], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+288], rax
	mov QWORD PTR [r8+296], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+304], rax
	mov QWORD PTR [r8+312], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+320], rax
	mov QWORD PTR [r8+328], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+336], rax
	mov QWORD PTR [r8+344], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+352], rax
	mov QWORD PTR [r8+360], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov QWORD PTR [r8+368], rax
	mov QWORD PTR [r8+376], rcx
	mov r10, rcx
	add r10, r10
	sbb r10, r10
	and r10, 135
	add rax, rax
	adc rcx, rcx
	xor rax, r10
	mov r10, rsi
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, r10
	add r10, rdi
	cmp r9, 8
	cmp r9, 16
	jb 22f
	movabs rax, 135
	vmovq xmm11, rax
	vpbroadcastq zmm11, xmm11
	vmovdqu32 zmm4, ZMMWORD PTR [r8+256]
	vmovdqu32 zmm5, ZMMWORD PTR [r8+320]
	vpsrldq zmm10, zmm4, 15
	vpclmulqdq zmm10, zmm10, zmm11, 0
	vpslldq zmm9, zmm4, 1
	vpxord zmm6, zmm9, zmm10
	vpsrldq zmm10, zmm5, 15
	vpclmulqdq zmm10, zmm10, zmm11, 0
	vpslldq zmm9, zmm5, 1
	vpxord zmm7, zmm9, zmm10
24:
	vmovdqu32 zmm0, ZMMWORD PTR [r11]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 zmm1, ZMMWORD PTR [r11+64]
	vpxord zmm1, zmm1, zmm5
	vmovdqu32 zmm2, ZMMWORD PTR [r11+128]
	vpxord zmm2, zmm2, zmm6
	vmovdqu32 zmm3, ZMMWORD PTR [r11+192]
	vpxord zmm3, zmm3, zmm7
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi]
	vpxord zmm0, zmm0, zmm8
	vpxord zmm1, zmm1, zmm8
	vpxord zmm2, zmm2, zmm8
	vpxord zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+16]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+32]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+48]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+64]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+80]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+96]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+112]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+128]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+144]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	cmp rsi, 10
	je 25f
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+160]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+176]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	cmp rsi, 12
	je 27f
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+192]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi+208]
	vaesenc zmm0, zmm0, zmm8
	vaesenc zmm1, zmm1, zmm8
	vaesenc zmm2, zmm2, zmm8
	vaesenc zmm3, zmm3, zmm8
	jmp 28f
27:
28:
	jmp 26f
25:
26:
	vbroadcasti32x4 zmm8, XMMWORD PTR [r10]
	vaesenclast zmm0, zmm0, zmm8
	vaesenclast zmm1, zmm1, zmm8
	vaesenclast zmm2, zmm2, zmm8
	vaesenclast zmm3, zmm3, zmm8
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 ZMMWORD PTR [r11], zmm0
	vpxord zmm1, zmm1, zmm5
	vmovdqu32 ZMMWORD PTR [r11+64], zmm1
	vpxord zmm2, zmm2, zmm6
	vmovdqu32 ZMMWORD PTR [r11+128], zmm2
	vpxord zmm3, zmm3, zmm7
	vmovdqu32 ZMMWORD PTR [r11+192], zmm3
	vpsrldq zmm10, zmm6, 15
	vpclmulqdq zmm10, zmm10, zmm11, 0
	vpslldq zmm9, zmm6, 1
	vpxord zmm4, zmm9, zmm10
	vpsrldq zmm10, zmm7, 15
	vpclmulqdq zmm10, zmm10, zmm11, 0
	vpslldq zmm9, zmm7, 1
	vpxord zmm5, zmm9, zmm10
	vpsrldq zmm10, zmm4, 15
	vpclmulqdq zmm10, zmm10, zmm11, 0
	vpslldq zmm9, zmm4, 1
	vpxord zmm6, zmm9, zmm10
	vpsrldq zmm10, zmm5, 15
	vpclmulqdq zmm10, zmm10, zmm11, 0
	vpslldq zmm9, zmm5, 1
	vpxord zmm7, zmm9, zmm10
	add r11, 256
	sub r9, 16
	cmp r9, 16
	jae 24b
	vmovdqu32 ZMMWORD PTR [r8+256], zmm4
	vmovdqu32 ZMMWORD PTR [r8+320], zmm5
	jmp 23f
22:
23:
	vzeroupper
	cmp r9, 8
	jb 29f
	movabs rax, 135
	vmovq xmm11, rax
	vinserti128 ymm11, ymm11, xmm11, 1
	vmovdqu ymm4, YMMWORD PTR [r8+256]
	vmovdqu ymm5, YMMWORD PTR [r8+288]
	vmovdqu ymm6, YMMWORD PTR [r8+320]
	vmovdqu ymm7, YMMWORD PTR [r8+352]
211:
	vmovdqu ymm0, YMMWORD PTR [r11]
	vpxor ymm0, ymm0, ymm4
	vmovdqu ymm1, YMMWORD PTR [r11+32]
	vpxor ymm1, ymm1, ymm5
	vmovdqu ymm2, YMMWORD PTR [r11+64]
	vpxor ymm2, ymm2, ymm6
	vmovdqu ymm3, YMMWORD PTR [r11+96]
	vpxor ymm3, ymm3, ymm7
	vbroadcasti128 ymm8, XMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm8
	vpxor ymm1, ymm1, ymm8
	vpxor ymm2, ymm2, ymm8
	vpxor ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+16]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+32]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+48]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+64]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+80]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+96]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+112]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+128]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+144]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	cmp rsi, 10
	je 212f
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+160]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+176]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	cmp rsi, 12
	je 214f
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+192]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi+208]
	vaesenc ymm0, ymm0, ymm8
	vaesenc ymm1, ymm1, ymm8
	vaesenc ymm2, ymm2, ymm8
	vaesenc ymm3, ymm3, ymm8
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	vbroadcasti128 ymm8, XMMWORD PTR [r10]
	vaesenclast ymm0, ymm0, ymm8
	vaesenclast ymm1, ymm1, ymm8
	vaesenclast ymm2, ymm2, ymm8
	vaesenclast ymm3, ymm3, ymm8
	vpxor ymm0, ymm0, ymm4
	vmovdqu YMMWORD PTR [r11], ymm0
	vpxor ymm1, ymm1, ymm5
	vmovdqu YMMWORD PTR [r11+32], ymm1
	vpxor ymm2, ymm2, ymm6
	vmovdqu YMMWORD PTR [r11+64], ymm2
	vpxor ymm3, ymm3, ymm7
	vmovdqu YMMWORD PTR [r11+96], ymm3
	vpsrldq ymm10, ymm4, 15
	vpclmulqdq ymm10, ymm10, ymm11, 0
	vpslldq ymm4, ymm4, 1
	vpxor ymm4, ymm4, ymm10
	vpsrldq ymm10, ymm5, 15
	vpclmulqdq ymm10, ymm10, ymm11, 0
	vpslldq ymm5, ymm5, 1
	vpxor ymm5, ymm5, ymm10
	vpsrldq ymm10, ymm6, 15
	vpclmulqdq ymm10, ymm10, ymm11, 0
	vpslldq ymm6, ymm6, 1
	vpxor ymm6, ymm6, ymm10
	vpsrldq ymm10, ymm7, 15
	vpclmulqdq ymm10, ymm10, ymm11, 0
	vpslldq ymm7, ymm7, 1
	vpxor ymm7, ymm7, ymm10
	add r11, 128
	sub r9, 8
	cmp r9, 8
	jae 211b
	vmovdqu YMMWORD PTR [r8+256], ymm4
	vmovdqu YMMWORD PTR [r8+288], ymm5
	vmovdqu YMMWORD PTR [r8+320], ymm6
	vmovdqu YMMWORD PTR [r8+352], ymm7
	vzeroupper
	jmp 210f
29:
210:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 216f
218:
	movdqu xmm0, XMMWORD PTR [r11]
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	cmp rsi, 10
	je 219f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 221f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 222f
221:
222:
	jmp 220f
219:
220:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 218b
	jmp 217f
216:
217:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6
