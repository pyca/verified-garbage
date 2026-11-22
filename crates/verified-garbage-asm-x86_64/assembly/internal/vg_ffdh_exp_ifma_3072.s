// The functions of `src/internal/vg_ffdh_exp_ifma_3072.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_exp_ifma_3072:
	mov r13d, 1952
20:
	cmp r13, 2912
	jb 21f
	mov r8, rbx
	add r8, r13
	sub r8, 480
	mov r9, rbx
	add r9, 992
	mov r11, rbx
	add r11, r13
	jmp 22f
21:
	mov r8, rbx
	add r8, r13
	sub r8, 1440
	mov r9, rbx
	add r9, 10016
	mov r11, r8
22:
	mov r10, rbx
	mov ecx, 4
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
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
23:
	mov rax, QWORD PTR [r9]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm0, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm0, 52
	vmovq xmm18, xmm18
	vpaddq ymm1, ymm1, ymm18
	valignq ymm0, ymm17, ymm0, 1
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm1, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm1, 52
	vmovq xmm18, xmm18
	vpaddq ymm2, ymm2, ymm18
	valignq ymm1, ymm17, ymm1, 1
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm2, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm2, 52
	vmovq xmm18, xmm18
	vpaddq ymm3, ymm3, ymm18
	valignq ymm2, ymm17, ymm2, 1
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm3, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm3, 52
	vmovq xmm18, xmm18
	vpaddq ymm4, ymm4, ymm18
	valignq ymm3, ymm17, ymm3, 1
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm4, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm4, 52
	vmovq xmm18, xmm18
	vpaddq ymm5, ymm5, ymm18
	valignq ymm4, ymm17, ymm4, 1
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm5, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm5, 52
	vmovq xmm18, xmm18
	vpaddq ymm6, ymm6, ymm18
	valignq ymm5, ymm17, ymm5, 1
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm6, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm6, 52
	vmovq xmm18, xmm18
	vpaddq ymm7, ymm7, ymm18
	valignq ymm6, ymm17, ymm6, 1
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm7, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm7, 52
	vmovq xmm18, xmm18
	vpaddq ymm8, ymm8, ymm18
	valignq ymm7, ymm17, ymm7, 1
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm8, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm8, 52
	vmovq xmm18, xmm18
	vpaddq ymm9, ymm9, ymm18
	valignq ymm8, ymm17, ymm8, 1
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm9, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm9, 52
	vmovq xmm18, xmm18
	vpaddq ymm10, ymm10, ymm18
	valignq ymm9, ymm17, ymm9, 1
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+320]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm10, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm10, 52
	vmovq xmm18, xmm18
	vpaddq ymm11, ymm11, ymm18
	valignq ymm10, ymm17, ymm10, 1
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+352]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm11, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm11, 52
	vmovq xmm18, xmm18
	vpaddq ymm12, ymm12, ymm18
	valignq ymm11, ymm17, ymm11, 1
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+384]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm12, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm12, 52
	vmovq xmm18, xmm18
	vpaddq ymm13, ymm13, ymm18
	valignq ymm12, ymm17, ymm12, 1
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+416]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm13, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm13, 52
	vmovq xmm18, xmm18
	vpaddq ymm14, ymm14, ymm18
	valignq ymm13, ymm17, ymm13, 1
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+448]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm14, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm14, 52
	vmovq xmm18, xmm18
	vpaddq ymm0, ymm0, ymm18
	valignq ymm14, ymm17, ymm14, 1
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+448]
	add r9, 8
	sub rcx, 1
	jne 23b
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
	vmovdqu64 YMMWORD PTR [r11+320], ymm10
	vmovdqu64 YMMWORD PTR [r11+352], ymm11
	vmovdqu64 YMMWORD PTR [r11+384], ymm12
	vmovdqu64 YMMWORD PTR [r11+416], ymm13
	vmovdqu64 YMMWORD PTR [r11+448], ymm14
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
	add rdx, QWORD PTR [r11+320]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+320], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+352]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+384]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+416]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+448]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+448], rax
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
	add rdx, QWORD PTR [r11+328]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+360]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+360], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+392]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+424]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+456]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+456], rax
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
	add rdx, QWORD PTR [r11+336]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+368]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+400]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+432]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+464]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+464], rax
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
	add rdx, QWORD PTR [r11+344]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+376]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+408]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+440]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+472]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+472], rax
	shr rdx, 52
	cmp r13, 2432
	je 24f
	jmp 25f
24:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+512]
	vmovdqu64 YMMWORD PTR [rbx+1952], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+544]
	vmovdqu64 YMMWORD PTR [rbx+1984], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+576]
	vmovdqu64 YMMWORD PTR [rbx+2016], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+608]
	vmovdqu64 YMMWORD PTR [rbx+2048], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+640]
	vmovdqu64 YMMWORD PTR [rbx+2080], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+672]
	vmovdqu64 YMMWORD PTR [rbx+2112], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+704]
	vmovdqu64 YMMWORD PTR [rbx+2144], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+736]
	vmovdqu64 YMMWORD PTR [rbx+2176], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+768]
	vmovdqu64 YMMWORD PTR [rbx+2208], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+800]
	vmovdqu64 YMMWORD PTR [rbx+2240], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+832]
	vmovdqu64 YMMWORD PTR [rbx+2272], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+864]
	vmovdqu64 YMMWORD PTR [rbx+2304], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+896]
	vmovdqu64 YMMWORD PTR [rbx+2336], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+928]
	vmovdqu64 YMMWORD PTR [rbx+2368], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+960]
	vmovdqu64 YMMWORD PTR [rbx+2400], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+992]
	vmovdqu64 YMMWORD PTR [rbx+2432], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1024]
	vmovdqu64 YMMWORD PTR [rbx+2464], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1056]
	vmovdqu64 YMMWORD PTR [rbx+2496], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1088]
	vmovdqu64 YMMWORD PTR [rbx+2528], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1120]
	vmovdqu64 YMMWORD PTR [rbx+2560], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1152]
	vmovdqu64 YMMWORD PTR [rbx+2592], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1184]
	vmovdqu64 YMMWORD PTR [rbx+2624], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1216]
	vmovdqu64 YMMWORD PTR [rbx+2656], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1248]
	vmovdqu64 YMMWORD PTR [rbx+2688], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1280]
	vmovdqu64 YMMWORD PTR [rbx+2720], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1312]
	vmovdqu64 YMMWORD PTR [rbx+2752], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1344]
	vmovdqu64 YMMWORD PTR [rbx+2784], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1376]
	vmovdqu64 YMMWORD PTR [rbx+2816], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1408]
	vmovdqu64 YMMWORD PTR [rbx+2848], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+1440]
	vmovdqu64 YMMWORD PTR [rbx+2880], ymm0
25:
	add r13, 480
	cmp r13, 9632
	jne 20b
	mov r13, rbp
26:
	cmp r13, 768
	je 27f
	mov r8, r13
	shr r8, 1
	mov rdx, r13
	and rdx, 1
	sub rdx, 1
	movzx eax, BYTE PTR [rbx+r8*1+9632]
	mov rcx, rax
	shr rcx, 4
	and rax, 15
	xor rcx, rax
	and rcx, rdx
	xor rax, rcx
	mov QWORD PTR [rbx+10496], rax
	mov r8, rbx
	add r8, 1952
	mov rdx, QWORD PTR [rbx+10496]
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
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
29:
	mov rax, rcx
	xor rax, rdx
	cmp rax, 1
	sbb rax, rax
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vmovdqu64 ymm16, YMMWORD PTR [r8]
	vpternlogq ymm0, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+32]
	vpternlogq ymm1, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+64]
	vpternlogq ymm2, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+96]
	vpternlogq ymm3, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+128]
	vpternlogq ymm4, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+160]
	vpternlogq ymm5, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+192]
	vpternlogq ymm6, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+224]
	vpternlogq ymm7, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+256]
	vpternlogq ymm8, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+288]
	vpternlogq ymm9, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+320]
	vpternlogq ymm10, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+352]
	vpternlogq ymm11, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+384]
	vpternlogq ymm12, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+416]
	vpternlogq ymm13, ymm16, ymm15, 248
	vmovdqu64 ymm16, YMMWORD PTR [r8+448]
	vpternlogq ymm14, ymm16, ymm15, 248
	add r8, 480
	add rcx, 1
	cmp rcx, 16
	jne 29b
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm1
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm2
	vmovdqu64 YMMWORD PTR [rbx+1568], ymm3
	vmovdqu64 YMMWORD PTR [rbx+1600], ymm4
	vmovdqu64 YMMWORD PTR [rbx+1632], ymm5
	vmovdqu64 YMMWORD PTR [rbx+1664], ymm6
	vmovdqu64 YMMWORD PTR [rbx+1696], ymm7
	vmovdqu64 YMMWORD PTR [rbx+1728], ymm8
	vmovdqu64 YMMWORD PTR [rbx+1760], ymm9
	vmovdqu64 YMMWORD PTR [rbx+1792], ymm10
	vmovdqu64 YMMWORD PTR [rbx+1824], ymm11
	vmovdqu64 YMMWORD PTR [rbx+1856], ymm12
	vmovdqu64 YMMWORD PTR [rbx+1888], ymm13
	vmovdqu64 YMMWORD PTR [rbx+1920], ymm14
	mov r15d, 5
	jmp 28f
27:
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10528]
	vmovdqu64 YMMWORD PTR [rbx+1472], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10560]
	vmovdqu64 YMMWORD PTR [rbx+1504], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10592]
	vmovdqu64 YMMWORD PTR [rbx+1536], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10624]
	vmovdqu64 YMMWORD PTR [rbx+1568], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10656]
	vmovdqu64 YMMWORD PTR [rbx+1600], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10688]
	vmovdqu64 YMMWORD PTR [rbx+1632], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10720]
	vmovdqu64 YMMWORD PTR [rbx+1664], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10752]
	vmovdqu64 YMMWORD PTR [rbx+1696], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10784]
	vmovdqu64 YMMWORD PTR [rbx+1728], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10816]
	vmovdqu64 YMMWORD PTR [rbx+1760], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10848]
	vmovdqu64 YMMWORD PTR [rbx+1792], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10880]
	vmovdqu64 YMMWORD PTR [rbx+1824], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10912]
	vmovdqu64 YMMWORD PTR [rbx+1856], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10944]
	vmovdqu64 YMMWORD PTR [rbx+1888], ymm0
	vmovdqu64 ymm0, YMMWORD PTR [rbx+10976]
	vmovdqu64 YMMWORD PTR [rbx+1920], ymm0
	mov r15d, 1
28:
210:
	cmp r15, 1
	je 211f
	mov r8, rbx
	add r8, 512
	mov r9, rbx
	add r9, 512
	mov r11, rbx
	add r11, 512
	jmp 212f
211:
	mov r8, rbx
	add r8, 512
	mov r9, rbx
	add r9, 1472
	mov r11, rbx
	add r11, 512
212:
	mov r10, rbx
	mov ecx, 4
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
	vpxorq ymm10, ymm10, ymm10
	vpxorq ymm11, ymm11, ymm11
	vpxorq ymm12, ymm12, ymm12
	vpxorq ymm13, ymm13, ymm13
	vpxorq ymm14, ymm14, ymm14
	vpxorq ymm15, ymm15, ymm15
	vpxorq ymm16, ymm16, ymm16
	vpxorq ymm17, ymm17, ymm17
213:
	mov rax, QWORD PTR [r9]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm0, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm0, 52
	vmovq xmm18, xmm18
	vpaddq ymm1, ymm1, ymm18
	valignq ymm0, ymm17, ymm0, 1
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+32]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm1, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm1, 52
	vmovq xmm18, xmm18
	vpaddq ymm2, ymm2, ymm18
	valignq ymm1, ymm17, ymm1, 1
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+64]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm2, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm2, 52
	vmovq xmm18, xmm18
	vpaddq ymm3, ymm3, ymm18
	valignq ymm2, ymm17, ymm2, 1
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+96]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm3, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm3, 52
	vmovq xmm18, xmm18
	vpaddq ymm4, ymm4, ymm18
	valignq ymm3, ymm17, ymm3, 1
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+128]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm4, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm4, 52
	vmovq xmm18, xmm18
	vpaddq ymm5, ymm5, ymm18
	valignq ymm4, ymm17, ymm4, 1
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+160]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm5, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm5, 52
	vmovq xmm18, xmm18
	vpaddq ymm6, ymm6, ymm18
	valignq ymm5, ymm17, ymm5, 1
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+192]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm6, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm6, 52
	vmovq xmm18, xmm18
	vpaddq ymm7, ymm7, ymm18
	valignq ymm6, ymm17, ymm6, 1
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+224]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm7, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm7, 52
	vmovq xmm18, xmm18
	vpaddq ymm8, ymm8, ymm18
	valignq ymm7, ymm17, ymm7, 1
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+256]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm8, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm8, 52
	vmovq xmm18, xmm18
	vpaddq ymm9, ymm9, ymm18
	valignq ymm8, ymm17, ymm8, 1
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+288]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm9, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm9, 52
	vmovq xmm18, xmm18
	vpaddq ymm10, ymm10, ymm18
	valignq ymm9, ymm17, ymm9, 1
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+320]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm10, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm10, 52
	vmovq xmm18, xmm18
	vpaddq ymm11, ymm11, ymm18
	valignq ymm10, ymm17, ymm10, 1
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+352]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm11, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm11, 52
	vmovq xmm18, xmm18
	vpaddq ymm12, ymm12, ymm18
	valignq ymm11, ymm17, ymm11, 1
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+384]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm12, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm12, 52
	vmovq xmm18, xmm18
	vpaddq ymm13, ymm13, ymm18
	valignq ymm12, ymm17, ymm12, 1
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+416]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm13, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm13, 52
	vmovq xmm18, xmm18
	vpaddq ymm14, ymm14, ymm18
	valignq ymm13, ymm17, ymm13, 1
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+448]
	mov rax, QWORD PTR [r9+448]
	vmovq xmm15, rax
	vpbroadcastq ymm15, xmm15
	vpmadd52luq ymm14, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm0, ymm15, YMMWORD PTR [r8+32]
	vpxorq ymm18, ymm18, ymm18
	vpmadd52luq ymm18, ymm14, YMMWORD PTR [r10+480]
	vpbroadcastq ymm16, xmm18
	vpmadd52huq ymm0, ymm15, YMMWORD PTR [r8]
	vpmadd52luq ymm14, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm0, ymm16, YMMWORD PTR [r10+32]
	vpsrlq ymm18, ymm14, 52
	vmovq xmm18, xmm18
	vpaddq ymm0, ymm0, ymm18
	valignq ymm14, ymm17, ymm14, 1
	vpmadd52huq ymm0, ymm16, YMMWORD PTR [r10]
	vpmadd52luq ymm1, ymm15, YMMWORD PTR [r8+64]
	vpmadd52huq ymm1, ymm15, YMMWORD PTR [r8+32]
	vpmadd52luq ymm1, ymm16, YMMWORD PTR [r10+64]
	vpmadd52huq ymm1, ymm16, YMMWORD PTR [r10+32]
	vpmadd52luq ymm2, ymm15, YMMWORD PTR [r8+96]
	vpmadd52huq ymm2, ymm15, YMMWORD PTR [r8+64]
	vpmadd52luq ymm2, ymm16, YMMWORD PTR [r10+96]
	vpmadd52huq ymm2, ymm16, YMMWORD PTR [r10+64]
	vpmadd52luq ymm3, ymm15, YMMWORD PTR [r8+128]
	vpmadd52huq ymm3, ymm15, YMMWORD PTR [r8+96]
	vpmadd52luq ymm3, ymm16, YMMWORD PTR [r10+128]
	vpmadd52huq ymm3, ymm16, YMMWORD PTR [r10+96]
	vpmadd52luq ymm4, ymm15, YMMWORD PTR [r8+160]
	vpmadd52huq ymm4, ymm15, YMMWORD PTR [r8+128]
	vpmadd52luq ymm4, ymm16, YMMWORD PTR [r10+160]
	vpmadd52huq ymm4, ymm16, YMMWORD PTR [r10+128]
	vpmadd52luq ymm5, ymm15, YMMWORD PTR [r8+192]
	vpmadd52huq ymm5, ymm15, YMMWORD PTR [r8+160]
	vpmadd52luq ymm5, ymm16, YMMWORD PTR [r10+192]
	vpmadd52huq ymm5, ymm16, YMMWORD PTR [r10+160]
	vpmadd52luq ymm6, ymm15, YMMWORD PTR [r8+224]
	vpmadd52huq ymm6, ymm15, YMMWORD PTR [r8+192]
	vpmadd52luq ymm6, ymm16, YMMWORD PTR [r10+224]
	vpmadd52huq ymm6, ymm16, YMMWORD PTR [r10+192]
	vpmadd52luq ymm7, ymm15, YMMWORD PTR [r8+256]
	vpmadd52huq ymm7, ymm15, YMMWORD PTR [r8+224]
	vpmadd52luq ymm7, ymm16, YMMWORD PTR [r10+256]
	vpmadd52huq ymm7, ymm16, YMMWORD PTR [r10+224]
	vpmadd52luq ymm8, ymm15, YMMWORD PTR [r8+288]
	vpmadd52huq ymm8, ymm15, YMMWORD PTR [r8+256]
	vpmadd52luq ymm8, ymm16, YMMWORD PTR [r10+288]
	vpmadd52huq ymm8, ymm16, YMMWORD PTR [r10+256]
	vpmadd52luq ymm9, ymm15, YMMWORD PTR [r8+320]
	vpmadd52huq ymm9, ymm15, YMMWORD PTR [r8+288]
	vpmadd52luq ymm9, ymm16, YMMWORD PTR [r10+320]
	vpmadd52huq ymm9, ymm16, YMMWORD PTR [r10+288]
	vpmadd52luq ymm10, ymm15, YMMWORD PTR [r8+352]
	vpmadd52huq ymm10, ymm15, YMMWORD PTR [r8+320]
	vpmadd52luq ymm10, ymm16, YMMWORD PTR [r10+352]
	vpmadd52huq ymm10, ymm16, YMMWORD PTR [r10+320]
	vpmadd52luq ymm11, ymm15, YMMWORD PTR [r8+384]
	vpmadd52huq ymm11, ymm15, YMMWORD PTR [r8+352]
	vpmadd52luq ymm11, ymm16, YMMWORD PTR [r10+384]
	vpmadd52huq ymm11, ymm16, YMMWORD PTR [r10+352]
	vpmadd52luq ymm12, ymm15, YMMWORD PTR [r8+416]
	vpmadd52huq ymm12, ymm15, YMMWORD PTR [r8+384]
	vpmadd52luq ymm12, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm12, ymm16, YMMWORD PTR [r10+384]
	vpmadd52luq ymm13, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm13, ymm15, YMMWORD PTR [r8+416]
	vpmadd52luq ymm13, ymm16, YMMWORD PTR [r10+448]
	vpmadd52huq ymm13, ymm16, YMMWORD PTR [r10+416]
	vpmadd52huq ymm14, ymm15, YMMWORD PTR [r8+448]
	vpmadd52huq ymm14, ymm16, YMMWORD PTR [r10+448]
	add r9, 8
	sub rcx, 1
	jne 213b
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
	vmovdqu64 YMMWORD PTR [r11+320], ymm10
	vmovdqu64 YMMWORD PTR [r11+352], ymm11
	vmovdqu64 YMMWORD PTR [r11+384], ymm12
	vmovdqu64 YMMWORD PTR [r11+416], ymm13
	vmovdqu64 YMMWORD PTR [r11+448], ymm14
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
	add rdx, QWORD PTR [r11+320]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+320], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+352]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+352], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+384]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+384], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+416]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+416], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+448]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+448], rax
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
	add rdx, QWORD PTR [r11+328]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+328], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+360]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+360], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+392]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+392], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+424]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+424], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+456]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+456], rax
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
	add rdx, QWORD PTR [r11+336]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+336], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+368]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+368], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+400]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+400], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+432]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+432], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+464]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+464], rax
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
	add rdx, QWORD PTR [r11+344]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+344], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+376]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+376], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+408]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+408], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+440]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+440], rax
	shr rdx, 52
	add rdx, QWORD PTR [r11+472]
	mov rax, rdx
	and rax, r12
	mov QWORD PTR [r11+472], rax
	shr rdx, 52
	sub r15, 1
	jne 210b
	add r13, 1
	cmp r13, 769
	jne 26b
	vzeroupper
	ret
	.p2align 6
