// The functions of `src/internal/vg_ffdh_exp_ifma_2048.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_exp_ifma_2048:
	mov r13d, 1312
20:
	cmp r13, 1952
	jb 21f
	mov r8, rbx
	add r8, r13
	sub r8, 320
	mov r9, rbx
	add r9, 672
	mov r11, rbx
	add r11, r13
	jmp 22f
21:
	mov r8, rbx
	add r8, r13
	sub r8, 960
	mov r9, rbx
	add r9, 6688
	mov r11, r8
22:
	mov r10, rbx
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm18, ymm18, ymm18
	mov rax, QWORD PTR [r9]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8]
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+8]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+40]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+72]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+104]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+136]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+168]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+200]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+232]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+264]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+296]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+16]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+48]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+80]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+112]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+144]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+176]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+208]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+240]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+272]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+304]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+24]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+56]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+88]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+120]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+152]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+184]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+216]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+248]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+280]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+312]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+160], ymm5
	vmovdqu64 YMMWORD PTR [r11+192], ymm6
	vmovdqu64 YMMWORD PTR [r11+224], ymm7
	vmovdqu64 YMMWORD PTR [r11+256], ymm8
	vmovdqu64 YMMWORD PTR [r11+288], ymm9
	movabs r12, 4503599627370495
	mov edx, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	cmp r13, 1632
	je 23f
	jmp 24f
23:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+352]
	vmovdqu64 YMMWORD PTR [rbx+1312], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+384]
	vmovdqu64 YMMWORD PTR [rbx+1344], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+416]
	vmovdqu64 YMMWORD PTR [rbx+1376], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+448]
	vmovdqu64 YMMWORD PTR [rbx+1408], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+480]
	vmovdqu64 YMMWORD PTR [rbx+1440], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+608]
	vmovdqu64 YMMWORD PTR [rbx+1568], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+640]
	vmovdqu64 YMMWORD PTR [rbx+1600], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+672]
	vmovdqu64 YMMWORD PTR [rbx+1632], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+704]
	vmovdqu64 YMMWORD PTR [rbx+1664], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+736]
	vmovdqu64 YMMWORD PTR [rbx+1696], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+768]
	vmovdqu64 YMMWORD PTR [rbx+1728], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+800]
	vmovdqu64 YMMWORD PTR [rbx+1760], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+832]
	vmovdqu64 YMMWORD PTR [rbx+1792], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+864]
	vmovdqu64 YMMWORD PTR [rbx+1824], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+896]
	vmovdqu64 YMMWORD PTR [rbx+1856], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+928]
	vmovdqu64 YMMWORD PTR [rbx+1888], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+960]
	vmovdqu64 YMMWORD PTR [rbx+1920], ymm0
24:
	add r13, 320
	cmp r13, 6432
	jne 20b
	mov r13, rbp
25:
	cmp r13, 512
	je 26f
	mov r8, r13
	shr r8, 1
	mov rdx, r13
	and rdx, 1
	sub rdx, 1
	movzx eax, BYTE PTR [rbx+r8*1+6432]
	mov rcx, rax
	shr rcx, 4
	and rax, 15
	xor rcx, rax
	and rcx, rdx
	xor rax, rcx
	mov QWORD PTR [rbx+7008], rax
	mov r8, rbx
	add r8, 1312
	mov rdx, QWORD PTR [rbx+7008]
	mov ecx, 0
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
28:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vmovdqu64 ymm11, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+256]
	vpternlogq ymm8, ymm11, ymm10, 248
	vmovdqu64 ymm11, YMMWORD PTR [r8+288]
	vpternlogq ymm9, ymm11, ymm10, 248
	add r8, 320
	add rcx, 1
	cmp rcx, 16
	jne 28b
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm1
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm2
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm3
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm4
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm5
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm6
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm7
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm8
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm9
	mov r15d, 5
	jmp 27f
26:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7040]
	vmovdqu64 YMMWORD PTR [rbx+992], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7072]
	vmovdqu64 YMMWORD PTR [rbx+1024], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7104]
	vmovdqu64 YMMWORD PTR [rbx+1056], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7136]
	vmovdqu64 YMMWORD PTR [rbx+1088], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7168]
	vmovdqu64 YMMWORD PTR [rbx+1120], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7200]
	vmovdqu64 YMMWORD PTR [rbx+1152], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7232]
	vmovdqu64 YMMWORD PTR [rbx+1184], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7264]
	vmovdqu64 YMMWORD PTR [rbx+1216], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7296]
	vmovdqu64 YMMWORD PTR [rbx+1248], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+7328]
	vmovdqu64 YMMWORD PTR [rbx+1280], ymm0
	mov r15d, 1
27:
29:
	cmp r15, 1
	je 210f
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 352
	mov r11, rbx
	add r11, 352
	jmp 211f
210:
	mov r8, rbx
	add r8, 352
	mov r9, rbx
	add r9, 992
	mov r11, rbx
	add r11, 352
211:
	mov r10, rbx
	vpxorq ymm0, ymm0, ymm0
	vpxorq ymm1, ymm1, ymm1
	vpxorq ymm2, ymm2, ymm2
	vpxorq ymm3, ymm3, ymm3
	vpxorq ymm4, ymm4, ymm4
	vpxorq ymm5, ymm5, ymm5
	vpxorq ymm6, ymm6, ymm6
	vpxorq ymm7, ymm7, ymm7
	vpxorq ymm8, ymm8, ymm8
	vpxorq ymm9, ymm9, ymm9
	vpxorq ymm18, ymm18, ymm18
	mov rax, QWORD PTR [r9]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8]
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+8]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+40]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+72]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+104]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+136]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+168]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+200]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+232]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+264]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+296]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+16]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+48]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+80]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+112]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+144]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+176]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+208]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+240]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+272]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+304]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+24]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm17
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm0, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+56]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm1, ymm1, ymm17
	vpaddq ymm1, ymm1, ymm15
	vpaddq ymm1, ymm1, ymm16
	vpsrlq ymm14, ymm0, 52
	vmovq xmm14, xmm14
	vpaddq ymm1, ymm1, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm1, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm0, ymm18, ymm0, 1
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+88]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm2, ymm2, ymm17
	vpaddq ymm2, ymm2, ymm15
	vpaddq ymm2, ymm2, ymm16
	vpsrlq ymm14, ymm1, 52
	vmovq xmm14, xmm14
	vpaddq ymm2, ymm2, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm2, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm1, ymm18, ymm1, 1
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+120]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm3, ymm3, ymm17
	vpaddq ymm3, ymm3, ymm15
	vpaddq ymm3, ymm3, ymm16
	vpsrlq ymm14, ymm2, 52
	vmovq xmm14, xmm14
	vpaddq ymm3, ymm3, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm3, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm2, ymm18, ymm2, 1
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+152]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm4, ymm4, ymm17
	vpaddq ymm4, ymm4, ymm15
	vpaddq ymm4, ymm4, ymm16
	vpsrlq ymm14, ymm3, 52
	vmovq xmm14, xmm14
	vpaddq ymm4, ymm4, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm4, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm3, ymm18, ymm3, 1
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+184]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm5, ymm5, ymm17
	vpaddq ymm5, ymm5, ymm15
	vpaddq ymm5, ymm5, ymm16
	vpsrlq ymm14, ymm4, 52
	vmovq xmm14, xmm14
	vpaddq ymm5, ymm5, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm5, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm4, ymm18, ymm4, 1
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+216]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm6, ymm6, ymm17
	vpaddq ymm6, ymm6, ymm15
	vpaddq ymm6, ymm6, ymm16
	vpsrlq ymm14, ymm5, 52
	vmovq xmm14, xmm14
	vpaddq ymm6, ymm6, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm6, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm5, ymm18, ymm5, 1
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+248]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm7, ymm7, ymm17
	vpaddq ymm7, ymm7, ymm15
	vpaddq ymm7, ymm7, ymm16
	vpsrlq ymm14, ymm6, 52
	vmovq xmm14, xmm14
	vpaddq ymm7, ymm7, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm7, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm6, ymm18, ymm6, 1
	vpmadd52luq ymm8, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+280]
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm10, YMMWORD PTR [r8]
	vpaddq ymm8, ymm8, ymm17
	vpaddq ymm8, ymm8, ymm15
	vpaddq ymm8, ymm8, ymm16
	vpsrlq ymm14, ymm7, 52
	vmovq xmm14, xmm14
	vpaddq ymm8, ymm8, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm8, YMMWORD PTR [r10+320]
	vpbroadcastq ymm12, xmm14
	valignq ymm7, ymm18, ymm7, 1
	vpmadd52luq ymm9, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm12, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm12, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm12, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm10, YMMWORD PTR [r8+32]
	vpmadd52huq ymm9, ymm10, YMMWORD PTR [r8]
	mov rax, QWORD PTR [r9+312]
	vmovq xmm11, rax
	vpbroadcastq ymm11, xmm11
	vpxorq ymm17, ymm17, ymm17
	vpmadd52luq ymm17, ymm11, YMMWORD PTR [r8]
	vpaddq ymm9, ymm9, ymm17
	vpaddq ymm9, ymm9, ymm15
	vpaddq ymm9, ymm9, ymm16
	vpsrlq ymm14, ymm8, 52
	vmovq xmm14, xmm14
	vpaddq ymm9, ymm9, ymm14
	vpxorq ymm14, ymm14, ymm14
	vpmadd52luq ymm14, ymm9, YMMWORD PTR [r10+320]
	vpbroadcastq ymm13, xmm14
	valignq ymm8, ymm18, ymm8, 1
	vpmadd52luq ymm0, ymm10, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm10, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm12, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm12, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm10, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm10, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm12, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm12, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm10, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm10, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm12, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm12, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm10, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm10, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm12, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm12, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm10, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm10, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm12, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm12, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm10, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm10, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm12, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm12, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm10, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm10, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm12, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm10, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm12, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm12, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm10, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm12, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm13, YMMWORD PTR [r10]
	vpxorq ymm15, ymm15, ymm15
	vpmadd52luq ymm15, ymm13, YMMWORD PTR [r10+32]
	vpxorq ymm16, ymm16, ymm16
	vpmadd52huq ymm16, ymm13, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm11, YMMWORD PTR [r8+32]
	vpmadd52huq ymm0, ymm11, YMMWORD PTR [r8]
	vpaddq ymm0, ymm0, ymm15
	vpaddq ymm0, ymm0, ymm16
	vpsrlq ymm14, ymm9, 52
	vmovq xmm14, xmm14
	vpaddq ymm0, ymm0, ymm14
	valignq ymm9, ymm18, ymm9, 1
	vpmadd52luq ymm1, ymm11, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm11, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm13, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm13, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm11, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm11, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm13, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm13, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm11, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm11, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm13, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm13, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm11, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm11, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm13, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm13, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm11, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm11, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm13, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm13, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm11, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm11, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm13, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm13, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm11, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm11, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm13, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm11, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm13, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm13, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm11, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm13, YMMWORD PTR [r10+288]
	vmovdqu64 YMMWORD PTR [r11], ymm0
	vmovdqu64 YMMWORD PTR [r11+32], ymm1
	vmovdqu64 YMMWORD PTR [r11+64], ymm2
	vmovdqu64 YMMWORD PTR [r11+96], ymm3
	vmovdqu64 YMMWORD PTR [r11+128], ymm4
	vmovdqu64 YMMWORD PTR [r11+160], ymm5
	vmovdqu64 YMMWORD PTR [r11+192], ymm6
	vmovdqu64 YMMWORD PTR [r11+224], ymm7
	vmovdqu64 YMMWORD PTR [r11+256], ymm8
	vmovdqu64 YMMWORD PTR [r11+288], ymm9
	movabs r12, 4503599627370495
	mov edx, 0
	add rdx, QWORD PTR [r11]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+32]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+32], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+64]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+64], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+96]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+96], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+128]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+128], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+160]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+160], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+192]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+192], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+224]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+224], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+256]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+256], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+288]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+288], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+8]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+8], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+40]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+40], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+72]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+72], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+104]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+104], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+136]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+136], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+168]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+168], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+200]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+200], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+232]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+232], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+264]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+264], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+296]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+296], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+16]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+16], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+48]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+48], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+80]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+80], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+112]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+112], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+144]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+144], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+176]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+176], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+208]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+208], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+240]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+240], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+272]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+272], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+304]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+304], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+24]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+24], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+56]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+56], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+88]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+88], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+120]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+120], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+152]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+152], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+184]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+184], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+216]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+216], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+248]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+248], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+280]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+280], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+312]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+312], rax
	shr rdx, 52
	sub r15, 1
	jne 29b
	add r13, 1
	cmp r13, 513
	jne 25b
	vzeroupper
	ret
	.p2align 6
