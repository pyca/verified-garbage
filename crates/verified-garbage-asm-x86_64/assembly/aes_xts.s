// The functions of `src/aes_xts.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt_vaes_vpclmul:
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
	jb 22f
	movabs rax, 135
	vmovq xmm11, rax
	vinserti128 ymm11, ymm11, xmm11, 1
	vmovdqu ymm4, YMMWORD PTR [r8+256]
	vmovdqu ymm5, YMMWORD PTR [r8+288]
	vmovdqu ymm6, YMMWORD PTR [r8+320]
	vmovdqu ymm7, YMMWORD PTR [r8+352]
24:
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
	je 25f
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
	je 27f
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
	jmp 28f
27:
28:
	jmp 26f
25:
26:
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
	jae 24b
	vmovdqu YMMWORD PTR [r8+256], ymm4
	vmovdqu YMMWORD PTR [r8+288], ymm5
	vmovdqu YMMWORD PTR [r8+320], ymm6
	vmovdqu YMMWORD PTR [r8+352], ymm7
	vzeroupper
	jmp 23f
22:
23:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 29f
211:
	movdqu xmm0, XMMWORD PTR [r11]
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
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
	je 212f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 214f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 211b
	jmp 210f
29:
210:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_aes_xts_decrypt_vaes_vpclmul:
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
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+16], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+32], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+48], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+64], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+80], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+96], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+112], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+128], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+144], xmm8
	cmp rsi, 10
	je 22f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+160], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+176], xmm8
	cmp rsi, 12
	je 24f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+192], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+208], xmm8
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	cmp r9, 8
	jb 26f
	movabs rax, 135
	vmovq xmm11, rax
	vinserti128 ymm11, ymm11, xmm11, 1
	vmovdqu ymm4, YMMWORD PTR [r8+256]
	vmovdqu ymm5, YMMWORD PTR [r8+288]
	vmovdqu ymm6, YMMWORD PTR [r8+320]
	vmovdqu ymm7, YMMWORD PTR [r8+352]
28:
	vmovdqu ymm0, YMMWORD PTR [r11]
	vpxor ymm0, ymm0, ymm4
	vmovdqu ymm1, YMMWORD PTR [r11+32]
	vpxor ymm1, ymm1, ymm5
	vmovdqu ymm2, YMMWORD PTR [r11+64]
	vpxor ymm2, ymm2, ymm6
	vmovdqu ymm3, YMMWORD PTR [r11+96]
	vpxor ymm3, ymm3, ymm7
	vbroadcasti128 ymm8, XMMWORD PTR [r10]
	vpxor ymm0, ymm0, ymm8
	vpxor ymm1, ymm1, ymm8
	vpxor ymm2, ymm2, ymm8
	vpxor ymm3, ymm3, ymm8
	cmp rsi, 10
	je 29f
	cmp rsi, 12
	je 211f
	vbroadcasti128 ymm8, XMMWORD PTR [r8+208]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+192]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	jmp 212f
211:
212:
	vbroadcasti128 ymm8, XMMWORD PTR [r8+176]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+160]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	jmp 210f
29:
210:
	vbroadcasti128 ymm8, XMMWORD PTR [r8+144]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+128]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+112]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+96]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+80]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+64]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+48]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+32]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [r8+16]
	vaesdec ymm0, ymm0, ymm8
	vaesdec ymm1, ymm1, ymm8
	vaesdec ymm2, ymm2, ymm8
	vaesdec ymm3, ymm3, ymm8
	vbroadcasti128 ymm8, XMMWORD PTR [rdi]
	vaesdeclast ymm0, ymm0, ymm8
	vaesdeclast ymm1, ymm1, ymm8
	vaesdeclast ymm2, ymm2, ymm8
	vaesdeclast ymm3, ymm3, ymm8
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
	jae 28b
	vmovdqu YMMWORD PTR [r8+256], ymm4
	vmovdqu YMMWORD PTR [r8+288], ymm5
	vmovdqu YMMWORD PTR [r8+320], ymm6
	vmovdqu YMMWORD PTR [r8+352], ymm7
	vzeroupper
	jmp 27f
26:
27:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 213f
215:
	movdqu xmm0, XMMWORD PTR [r11]
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	cmp rsi, 10
	je 216f
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	jmp 219f
218:
219:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 215b
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_aes_xts_encrypt_aesni_pclmul:
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
	jb 22f
	movabs rax, 135
	vmovq xmm11, rax
	mov rax, r8
	add rax, 256
24:
	movdqu xmm0, XMMWORD PTR [r11]
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu xmm1, XMMWORD PTR [r11+16]
	vpxor xmm1, xmm1, XMMWORD PTR [rax+16]
	movdqu xmm2, XMMWORD PTR [r11+32]
	vpxor xmm2, xmm2, XMMWORD PTR [rax+32]
	movdqu xmm3, XMMWORD PTR [r11+48]
	vpxor xmm3, xmm3, XMMWORD PTR [rax+48]
	movdqu xmm4, XMMWORD PTR [r11+64]
	vpxor xmm4, xmm4, XMMWORD PTR [rax+64]
	movdqu xmm5, XMMWORD PTR [r11+80]
	vpxor xmm5, xmm5, XMMWORD PTR [rax+80]
	movdqu xmm6, XMMWORD PTR [r11+96]
	vpxor xmm6, xmm6, XMMWORD PTR [rax+96]
	movdqu xmm7, XMMWORD PTR [r11+112]
	vpxor xmm7, xmm7, XMMWORD PTR [rax+112]
	movdqu xmm8, XMMWORD PTR [rdi]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 10
	je 25f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	cmp rsi, 12
	je 27f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	aesenc xmm1, xmm8
	aesenc xmm2, xmm8
	aesenc xmm3, xmm8
	aesenc xmm4, xmm8
	aesenc xmm5, xmm8
	aesenc xmm6, xmm8
	aesenc xmm7, xmm8
	jmp 28f
27:
28:
	jmp 26f
25:
26:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	aesenclast xmm1, xmm8
	aesenclast xmm2, xmm8
	aesenclast xmm3, xmm8
	aesenclast xmm4, xmm8
	aesenclast xmm5, xmm8
	aesenclast xmm6, xmm8
	aesenclast xmm7, xmm8
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu XMMWORD PTR [r11], xmm0
	vpxor xmm1, xmm1, XMMWORD PTR [rax+16]
	movdqu XMMWORD PTR [r11+16], xmm1
	vpxor xmm2, xmm2, XMMWORD PTR [rax+32]
	movdqu XMMWORD PTR [r11+32], xmm2
	vpxor xmm3, xmm3, XMMWORD PTR [rax+48]
	movdqu XMMWORD PTR [r11+48], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rax+64]
	movdqu XMMWORD PTR [r11+64], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rax+80]
	movdqu XMMWORD PTR [r11+80], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rax+96]
	movdqu XMMWORD PTR [r11+96], xmm6
	vpxor xmm7, xmm7, XMMWORD PTR [rax+112]
	movdqu XMMWORD PTR [r11+112], xmm7
	vmovdqu xmm9, XMMWORD PTR [rax]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+16]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+16], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+32]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+32], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+48]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+48], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+64]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+64], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+80]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+80], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+96]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+96], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+112]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+112], xmm9
	add r11, 128
	sub r9, 8
	cmp r9, 8
	jae 24b
	jmp 23f
22:
23:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 29f
211:
	movdqu xmm0, XMMWORD PTR [r11]
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
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
	je 212f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesenc xmm0, xmm8
	cmp rsi, 12
	je 214f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesenc xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesenc xmm0, xmm8
	jmp 215f
214:
215:
	jmp 213f
212:
213:
	movdqu xmm8, XMMWORD PTR [r10]
	aesenclast xmm0, xmm8
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 211b
	jmp 210f
29:
210:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_aes_xts_decrypt_aesni_pclmul:
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
	movdqu xmm8, XMMWORD PTR [rdi+16]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+16], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+32]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+32], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+48]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+48], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+64]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+64], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+80]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+80], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+96]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+96], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+112]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+112], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+128]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+128], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+144]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+144], xmm8
	cmp rsi, 10
	je 22f
	movdqu xmm8, XMMWORD PTR [rdi+160]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+160], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+176]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+176], xmm8
	cmp rsi, 12
	je 24f
	movdqu xmm8, XMMWORD PTR [rdi+192]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+192], xmm8
	movdqu xmm8, XMMWORD PTR [rdi+208]
	aesimc xmm8, xmm8
	movdqu XMMWORD PTR [r8+208], xmm8
	jmp 25f
24:
25:
	jmp 23f
22:
23:
	cmp r9, 8
	jb 26f
	movabs rax, 135
	vmovq xmm11, rax
	mov rax, r8
	add rax, 256
28:
	movdqu xmm0, XMMWORD PTR [r11]
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu xmm1, XMMWORD PTR [r11+16]
	vpxor xmm1, xmm1, XMMWORD PTR [rax+16]
	movdqu xmm2, XMMWORD PTR [r11+32]
	vpxor xmm2, xmm2, XMMWORD PTR [rax+32]
	movdqu xmm3, XMMWORD PTR [r11+48]
	vpxor xmm3, xmm3, XMMWORD PTR [rax+48]
	movdqu xmm4, XMMWORD PTR [r11+64]
	vpxor xmm4, xmm4, XMMWORD PTR [rax+64]
	movdqu xmm5, XMMWORD PTR [r11+80]
	vpxor xmm5, xmm5, XMMWORD PTR [rax+80]
	movdqu xmm6, XMMWORD PTR [r11+96]
	vpxor xmm6, xmm6, XMMWORD PTR [rax+96]
	movdqu xmm7, XMMWORD PTR [r11+112]
	vpxor xmm7, xmm7, XMMWORD PTR [rax+112]
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	pxor xmm1, xmm8
	pxor xmm2, xmm8
	pxor xmm3, xmm8
	pxor xmm4, xmm8
	pxor xmm5, xmm8
	pxor xmm6, xmm8
	pxor xmm7, xmm8
	cmp rsi, 10
	je 29f
	cmp rsi, 12
	je 211f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 212f
211:
212:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	jmp 210f
29:
210:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	aesdec xmm1, xmm8
	aesdec xmm2, xmm8
	aesdec xmm3, xmm8
	aesdec xmm4, xmm8
	aesdec xmm5, xmm8
	aesdec xmm6, xmm8
	aesdec xmm7, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	aesdeclast xmm1, xmm8
	aesdeclast xmm2, xmm8
	aesdeclast xmm3, xmm8
	aesdeclast xmm4, xmm8
	aesdeclast xmm5, xmm8
	aesdeclast xmm6, xmm8
	aesdeclast xmm7, xmm8
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu XMMWORD PTR [r11], xmm0
	vpxor xmm1, xmm1, XMMWORD PTR [rax+16]
	movdqu XMMWORD PTR [r11+16], xmm1
	vpxor xmm2, xmm2, XMMWORD PTR [rax+32]
	movdqu XMMWORD PTR [r11+32], xmm2
	vpxor xmm3, xmm3, XMMWORD PTR [rax+48]
	movdqu XMMWORD PTR [r11+48], xmm3
	vpxor xmm4, xmm4, XMMWORD PTR [rax+64]
	movdqu XMMWORD PTR [r11+64], xmm4
	vpxor xmm5, xmm5, XMMWORD PTR [rax+80]
	movdqu XMMWORD PTR [r11+80], xmm5
	vpxor xmm6, xmm6, XMMWORD PTR [rax+96]
	movdqu XMMWORD PTR [r11+96], xmm6
	vpxor xmm7, xmm7, XMMWORD PTR [rax+112]
	movdqu XMMWORD PTR [r11+112], xmm7
	vmovdqu xmm9, XMMWORD PTR [rax]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+16]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+16], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+32]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+32], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+48]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+48], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+64]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+64], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+80]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+80], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+96]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+96], xmm9
	vmovdqu xmm9, XMMWORD PTR [rax+112]
	vpsrldq xmm10, xmm9, 15
	vpclmulqdq xmm10, xmm10, xmm11, 0
	vpslldq xmm9, xmm9, 1
	vpxor xmm9, xmm9, xmm10
	vmovdqu XMMWORD PTR [rax+112], xmm9
	add r11, 128
	sub r9, 8
	cmp r9, 8
	jae 28b
	jmp 27f
26:
27:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 213f
215:
	movdqu xmm0, XMMWORD PTR [r11]
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	cmp rsi, 10
	je 216f
	cmp rsi, 12
	je 218f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	jmp 219f
218:
219:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	jmp 217f
216:
217:
	movdqu xmm8, XMMWORD PTR [r8+144]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+128]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+112]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+96]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+80]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+64]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+48]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+32]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+16]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [rdi]
	aesdeclast xmm0, xmm8
	vpxor xmm0, xmm0, XMMWORD PTR [rax]
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 215b
	jmp 214f
213:
214:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6

vg_aes_xts_encrypt_aesni:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_encrypt_blocks_aesni}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_aes_xts_decrypt_aesni:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_decrypt_blocks_aesni}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_aes_xts_encrypt:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_encrypt_blocks}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_aes_xts_decrypt:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_decrypt_blocks}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_aes_xts_encrypt_vaes:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_encrypt_blocks_vaes}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_aes_xts_decrypt_vaes:
	mov QWORD PTR [r9+2064], rbx
	mov QWORD PTR [r9+2072], rbp
	mov QWORD PTR [r9+2080], r12
	mov QWORD PTR [r9+2088], r13
	mov QWORD PTR [r9+2096], r14
	mov QWORD PTR [r9+2104], r15
	mov rbx, rdi
	mov rbp, rsi
	mov r12, rdx
	mov r13, rcx
	mov r14, r8
	mov r15, r9
	test r14, r14
	je 20f
	mov r10, r13
	mov r11, r14
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
22:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 22b
	mov r13, r10
	mov r14, r11
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r13
	mov rcx, r14
	mov r8, r15
	call {vg_aes_decrypt_blocks_vaes}
	mov rax, QWORD PTR [r12]
	mov rcx, QWORD PTR [r12+8]
23:
	mov rdx, QWORD PTR [r13]
	xor rdx, rax
	mov QWORD PTR [r13], rdx
	mov rdx, QWORD PTR [r13+8]
	xor rdx, rcx
	mov QWORD PTR [r13+8], rdx
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	add r13, 16
	sub r14, 1
	jne 23b
	mov QWORD PTR [r12], rax
	mov QWORD PTR [r12+8], rcx
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2064]
	mov rbp, QWORD PTR [r15+2072]
	mov r12, QWORD PTR [r15+2080]
	mov r13, QWORD PTR [r15+2088]
	mov r14, QWORD PTR [r15+2096]
	mov r15, QWORD PTR [r15+2104]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_aesni:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_aesni:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_aesni}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_aesni_pclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_aesni_pclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_aesni_pclmul}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_aesni_pclmul}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_vaes:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_vaes:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_vaes}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_encrypt_unit_vaes_vpclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	jmp 21f
20:
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6

vg_aes_xts_decrypt_unit_vaes_vpclmul:
	mov rax, QWORD PTR [rsp+8]
	mov QWORD PTR [rax+2208], rbx
	mov QWORD PTR [rax+2216], rbp
	mov QWORD PTR [rax+2224], r12
	mov QWORD PTR [rax+2232], r13
	mov QWORD PTR [rax+2240], r14
	mov QWORD PTR [rax+2248], r15
	mov r15, rax
	mov rbx, rdi
	mov rbp, rdx
	mov r12, r8
	mov r13, r9
	mov rax, QWORD PTR [rcx]
	mov QWORD PTR [r15+2176], rax
	mov rax, QWORD PTR [rcx+8]
	mov QWORD PTR [r15+2184], rax
	mov eax, 0
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rax
	mov rdi, rsi
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov rcx, r15
	add rcx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_encrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	je 20f
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	sub r8, 1
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	mov rax, QWORD PTR [r15+2176]
	mov rcx, QWORD PTR [r15+2184]
	mov rdx, rcx
	add rdx, rdx
	sbb rdx, rdx
	and rdx, 135
	add rax, rax
	adc rcx, rcx
	xor rax, rdx
	mov QWORD PTR [r15+2192], rax
	mov QWORD PTR [r15+2200], rcx
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2192
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	mov rax, r13
	shr rax, 4
	shl rax, 4
	mov r8, r13
	sub r8, rax
	mov rdx, r12
	add rdx, rax
	sub rdx, 16
	mov ecx, 0
22:
	movzx eax, BYTE PTR [rdx+rcx*1]
	movzx r9d, BYTE PTR [rdx+rcx*1+16]
	mov BYTE PTR [rdx+rcx*1], r9b
	mov BYTE PTR [rdx+rcx*1+16], al
	add rcx, 1
	cmp rcx, r8
	jne 22b
	mov rcx, rdx
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov r8d, 1
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
	jmp 21f
20:
	mov rdi, rbx
	mov rsi, rbp
	mov rdx, r15
	add rdx, 2176
	mov rcx, r12
	mov r8, r13
	shr r8, 4
	mov r9, r15
	call {vg_aes_xts_decrypt_vaes_vpclmul}
21:
	mov rbx, QWORD PTR [r15+2208]
	mov rbp, QWORD PTR [r15+2216]
	mov r12, QWORD PTR [r15+2224]
	mov r13, QWORD PTR [r15+2232]
	mov r14, QWORD PTR [r15+2240]
	mov r15, QWORD PTR [r15+2248]
	ret
	.p2align 6
