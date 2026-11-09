// The functions of `src/internal/vg_aes_xts_decrypt_to_vaes_vpclmul_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_decrypt_to_vaes_vpclmul_avx512:
	test r8, r8
	je 20f
	sub rcx, r10
	mov QWORD PTR [r9+248], rcx
	mov rcx, r10
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
	mov rcx, QWORD PTR [r8+248]
	cmp r9, 8
	cmp r9, 16
	jb 26f
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
28:
	vmovdqu32 zmm0, ZMMWORD PTR [r11+rcx*1]
	vpxord zmm0, zmm0, zmm4
	vmovdqu32 zmm1, ZMMWORD PTR [r11+rcx*1+64]
	vpxord zmm1, zmm1, zmm5
	vmovdqu32 zmm2, ZMMWORD PTR [r11+rcx*1+128]
	vpxord zmm2, zmm2, zmm6
	vmovdqu32 zmm3, ZMMWORD PTR [r11+rcx*1+192]
	vpxord zmm3, zmm3, zmm7
	vbroadcasti32x4 zmm8, XMMWORD PTR [r10]
	vpxord zmm0, zmm0, zmm8
	vpxord zmm1, zmm1, zmm8
	vpxord zmm2, zmm2, zmm8
	vpxord zmm3, zmm3, zmm8
	cmp rsi, 10
	je 29f
	cmp rsi, 12
	je 211f
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+208]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+192]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	jmp 212f
211:
212:
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+176]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+160]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	jmp 210f
29:
210:
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+144]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+128]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+112]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+96]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+80]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+64]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+48]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+32]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [r8+16]
	vaesdec zmm0, zmm0, zmm8
	vaesdec zmm1, zmm1, zmm8
	vaesdec zmm2, zmm2, zmm8
	vaesdec zmm3, zmm3, zmm8
	vbroadcasti32x4 zmm8, XMMWORD PTR [rdi]
	vaesdeclast zmm0, zmm0, zmm8
	vaesdeclast zmm1, zmm1, zmm8
	vaesdeclast zmm2, zmm2, zmm8
	vaesdeclast zmm3, zmm3, zmm8
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
	jae 28b
	vmovdqu32 ZMMWORD PTR [r8+256], zmm4
	vmovdqu32 ZMMWORD PTR [r8+320], zmm5
	jmp 27f
26:
27:
	vzeroupper
	cmp r9, 8
	jb 213f
	movabs rax, 135
	vmovq xmm11, rax
	vinserti128 ymm11, ymm11, xmm11, 1
	vmovdqu ymm4, YMMWORD PTR [r8+256]
	vmovdqu ymm5, YMMWORD PTR [r8+288]
	vmovdqu ymm6, YMMWORD PTR [r8+320]
	vmovdqu ymm7, YMMWORD PTR [r8+352]
215:
	vmovdqu ymm0, YMMWORD PTR [r11+rcx*1]
	vpxor ymm0, ymm0, ymm4
	vmovdqu ymm1, YMMWORD PTR [r11+rcx*1+32]
	vpxor ymm1, ymm1, ymm5
	vmovdqu ymm2, YMMWORD PTR [r11+rcx*1+64]
	vpxor ymm2, ymm2, ymm6
	vmovdqu ymm3, YMMWORD PTR [r11+rcx*1+96]
	vpxor ymm3, ymm3, ymm7
	vbroadcasti128 ymm8, XMMWORD PTR [r10]
	vpxor ymm0, ymm0, ymm8
	vpxor ymm1, ymm1, ymm8
	vpxor ymm2, ymm2, ymm8
	vpxor ymm3, ymm3, ymm8
	cmp rsi, 10
	je 216f
	cmp rsi, 12
	je 218f
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
	jmp 219f
218:
219:
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
	jmp 217f
216:
217:
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
	jae 215b
	vmovdqu YMMWORD PTR [r8+256], ymm4
	vmovdqu YMMWORD PTR [r8+288], ymm5
	vmovdqu YMMWORD PTR [r8+320], ymm6
	vmovdqu YMMWORD PTR [r8+352], ymm7
	vzeroupper
	jmp 214f
213:
214:
	mov rax, r8
	add rax, 256
	test r9, r9
	je 220f
222:
	movdqu xmm0, XMMWORD PTR [r11+rcx*1]
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu xmm8, XMMWORD PTR [r10]
	pxor xmm0, xmm8
	cmp rsi, 10
	je 223f
	cmp rsi, 12
	je 225f
	movdqu xmm8, XMMWORD PTR [r8+208]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+192]
	aesdec xmm0, xmm8
	jmp 226f
225:
226:
	movdqu xmm8, XMMWORD PTR [r8+176]
	aesdec xmm0, xmm8
	movdqu xmm8, XMMWORD PTR [r8+160]
	aesdec xmm0, xmm8
	jmp 224f
223:
224:
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
	movdqu xmm9, XMMWORD PTR [rax]
	pxor xmm0, xmm9
	movdqu XMMWORD PTR [r11], xmm0
	add r11, 16
	add rax, 16
	sub r9, 1
	jne 222b
	jmp 221f
220:
221:
	mov rcx, QWORD PTR [rax]
	mov QWORD PTR [rdx], rcx
	mov rcx, QWORD PTR [rax+8]
	mov QWORD PTR [rdx+8], rcx
	jmp 21f
20:
21:
	ret
	.p2align 6
