// The functions of `src/internal/vg_mlkem768_kpke_keygen_ntt.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_kpke_keygen_ntt:
	mov QWORD PTR [r8+3072], rbp
	mov QWORD PTR [r8+3080], r12
	mov QWORD PTR [r8+3088], r13
	mov QWORD PTR [r8+3096], r14
	mov QWORD PTR [r8+3104], r15
	mov QWORD PTR [r8+3112], rbx
	mov rbx, r8
	mov r13, rdi
	mov r12, rsi
	mov rbp, rdx
	mov r15, rcx
	mov rdx, r15
	add rdx, 0
	mov r9, r12
	add r9, 0
	pxor xmm4, xmm4
	mov ecx, 32
20:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqu XMMWORD PTR [r9], xmm0
	movdqu XMMWORD PTR [r9+16], xmm1
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 20b
	mov rdx, r15
	add rdx, 512
	mov r9, r12
	add r9, 1024
	pxor xmm4, xmm4
	mov ecx, 32
21:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqu XMMWORD PTR [r9], xmm0
	movdqu XMMWORD PTR [r9+16], xmm1
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 21b
	mov rdx, r15
	add rdx, 1024
	mov r9, r12
	add r9, 2048
	pxor xmm4, xmm4
	mov ecx, 32
22:
	movdqu xmm0, XMMWORD PTR [rdx]
	movdqa xmm1, xmm0
	punpcklwd xmm0, xmm4
	punpckhwd xmm1, xmm4
	movdqu XMMWORD PTR [r9], xmm0
	movdqu XMMWORD PTR [r9+16], xmm1
	add r9, 32
	add rdx, 16
	sub rcx, 1
	jne 22b
	add r15, 1536
	mov r14d, 3
	stmxcsr DWORD PTR [rbx+768]
	mov r11d, DWORD PTR [rbx+768]
	and r11d, 65535
	mov eax, 8127
	mov DWORD PTR [rbx+772], eax
	ldmxcsr DWORD PTR [rbx+772]
	lfence
23:
	mov rdi, r12
	mov rsi, rbx
	mov r10, r12
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	lea r8, {VG_MLKEM_NTT_ZETAS}
	vmovdqu ymm12, YMMWORD PTR [r8+64]
	vmovdqu ymm13, YMMWORD PTR [r8+96]
	vmovdqu ymm4, YMMWORD PTR [rdi]
	vmovdqu ymm3, YMMWORD PTR [rdi+32]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+512]
	vmovdqu ymm3, YMMWORD PTR [rdi+544]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+256], ymm4
	vmovdqu YMMWORD PTR [rsi+512], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+576]
	vmovdqu ymm3, YMMWORD PTR [rdi+608]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+288], ymm4
	vmovdqu YMMWORD PTR [rsi+544], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+128]
	vmovdqu ymm3, YMMWORD PTR [rdi+160]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+640]
	vmovdqu ymm3, YMMWORD PTR [rdi+672]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+320], ymm4
	vmovdqu YMMWORD PTR [rsi+576], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+192]
	vmovdqu ymm3, YMMWORD PTR [rdi+224]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+704]
	vmovdqu ymm3, YMMWORD PTR [rdi+736]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+352], ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+256]
	vmovdqu ymm3, YMMWORD PTR [rdi+288]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+768]
	vmovdqu ymm3, YMMWORD PTR [rdi+800]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+384], ymm4
	vmovdqu YMMWORD PTR [rsi+640], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+320]
	vmovdqu ymm3, YMMWORD PTR [rdi+352]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+832]
	vmovdqu ymm3, YMMWORD PTR [rdi+864]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+416], ymm4
	vmovdqu YMMWORD PTR [rsi+672], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+384]
	vmovdqu ymm3, YMMWORD PTR [rdi+416]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+896]
	vmovdqu ymm3, YMMWORD PTR [rdi+928]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+448], ymm4
	vmovdqu YMMWORD PTR [rsi+704], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+448]
	vmovdqu ymm3, YMMWORD PTR [rdi+480]
	vpackssdw ymm4, ymm4, ymm3
	vpermq ymm4, ymm4, 216
	vmovdqu ymm5, YMMWORD PTR [rdi+960]
	vmovdqu ymm3, YMMWORD PTR [rdi+992]
	vpackssdw ymm5, ymm5, ymm3
	vpermq ymm5, ymm5, 216
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+480], ymm4
	vmovdqu YMMWORD PTR [rsi+736], ymm6
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu ymm2, YMMWORD PTR [rsi+320]
	vmovdqu ymm3, YMMWORD PTR [rsi+352]
	vmovdqu ymm4, YMMWORD PTR [rsi+384]
	vmovdqu ymm5, YMMWORD PTR [rsi+416]
	vmovdqu ymm6, YMMWORD PTR [rsi+448]
	vmovdqu ymm7, YMMWORD PTR [rsi+480]
	vmovdqu ymm8, YMMWORD PTR [r8+128]
	vmovdqu ymm9, YMMWORD PTR [r8+160]
	vpmullw ymm10, ymm4, ymm9
	vpmullw ymm12, ymm5, ymm9
	vpmulhw ymm4, ymm4, ymm8
	vpmulhw ymm5, ymm5, ymm8
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm10
	vpsubw ymm5, ymm5, ymm12
	vpsubw ymm11, ymm0, ymm4
	vpsubw ymm13, ymm1, ymm5
	vpaddw ymm0, ymm0, ymm4
	vpaddw ymm1, ymm1, ymm5
	vmovdqu ymm14, YMMWORD PTR [r8+128]
	vmovdqu ymm10, YMMWORD PTR [r8+160]
	vpmullw ymm4, ymm6, ymm10
	vpmullw ymm5, ymm7, ymm10
	vpmulhw ymm6, ymm6, ymm14
	vpmulhw ymm7, ymm7, ymm14
	vpmulhw ymm4, ymm4, ymm15
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm6, ymm6, ymm4
	vpsubw ymm7, ymm7, ymm5
	vpsubw ymm12, ymm2, ymm6
	vpsubw ymm8, ymm3, ymm7
	vpaddw ymm2, ymm2, ymm6
	vpaddw ymm3, ymm3, ymm7
	vmovdqu ymm9, YMMWORD PTR [r8+192]
	vmovdqu ymm4, YMMWORD PTR [r8+224]
	vpmullw ymm6, ymm2, ymm4
	vpmullw ymm7, ymm3, ymm4
	vpmulhw ymm2, ymm2, ymm9
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm6, ymm6, ymm15
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm2, ymm2, ymm6
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm5, ymm0, ymm2
	vpsubw ymm14, ymm1, ymm3
	vpaddw ymm0, ymm0, ymm2
	vpaddw ymm1, ymm1, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+256]
	vmovdqu ymm6, YMMWORD PTR [r8+288]
	vpmullw ymm2, ymm12, ymm6
	vpmullw ymm3, ymm8, ymm6
	vpmulhw ymm12, ymm12, ymm10
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm2
	vpsubw ymm8, ymm8, ymm3
	vpsubw ymm7, ymm11, ymm12
	vpsubw ymm9, ymm13, ymm8
	vpaddw ymm11, ymm11, ymm12
	vpaddw ymm13, ymm13, ymm8
	vmovdqu ymm4, YMMWORD PTR [r8+320]
	vmovdqu ymm2, YMMWORD PTR [r8+352]
	vpmullw ymm12, ymm1, ymm2
	vpmulhw ymm1, ymm1, ymm4
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm1, ymm1, ymm12
	vpsubw ymm3, ymm0, ymm1
	vpaddw ymm0, ymm0, ymm1
	vmovdqu ymm8, YMMWORD PTR [r8+384]
	vmovdqu ymm10, YMMWORD PTR [r8+416]
	vpmullw ymm6, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vpsubw ymm12, ymm5, ymm14
	vpaddw ymm5, ymm5, ymm14
	vmovdqu ymm1, YMMWORD PTR [r8+448]
	vmovdqu ymm4, YMMWORD PTR [r8+480]
	vpmullw ymm2, ymm13, ymm4
	vpmulhw ymm13, ymm13, ymm1
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm13, ymm13, ymm2
	vpsubw ymm6, ymm11, ymm13
	vpaddw ymm11, ymm11, ymm13
	vmovdqu ymm14, YMMWORD PTR [r8+512]
	vmovdqu ymm8, YMMWORD PTR [r8+544]
	vpmullw ymm10, ymm9, ymm8
	vpmulhw ymm9, ymm9, ymm14
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm9, ymm9, ymm10
	vpsubw ymm2, ymm7, ymm9
	vpaddw ymm7, ymm7, ymm9
	vperm2i128 ymm13, ymm0, ymm3, 32
	vperm2i128 ymm3, ymm0, ymm3, 49
	vperm2i128 ymm1, ymm5, ymm12, 32
	vperm2i128 ymm12, ymm5, ymm12, 49
	vperm2i128 ymm4, ymm11, ymm6, 32
	vperm2i128 ymm6, ymm11, ymm6, 49
	vperm2i128 ymm10, ymm7, ymm2, 32
	vperm2i128 ymm2, ymm7, ymm2, 49
	vmovdqu ymm9, YMMWORD PTR [r8+576]
	vmovdqu ymm14, YMMWORD PTR [r8+608]
	vpmullw ymm8, ymm3, ymm14
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm3, ymm3, ymm8
	vpsubw ymm0, ymm13, ymm3
	vpaddw ymm13, ymm13, ymm3
	vmovdqu ymm5, YMMWORD PTR [r8+640]
	vmovdqu ymm11, YMMWORD PTR [r8+672]
	vpmullw ymm7, ymm12, ymm11
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm12, ymm12, ymm7
	vpsubw ymm8, ymm1, ymm12
	vpaddw ymm1, ymm1, ymm12
	vmovdqu ymm3, YMMWORD PTR [r8+704]
	vmovdqu ymm9, YMMWORD PTR [r8+736]
	vpmullw ymm14, ymm6, ymm9
	vpmulhw ymm6, ymm6, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm6, ymm6, ymm14
	vpsubw ymm7, ymm4, ymm6
	vpaddw ymm4, ymm4, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+768]
	vmovdqu ymm5, YMMWORD PTR [r8+800]
	vpmullw ymm11, ymm2, ymm5
	vpmulhw ymm2, ymm2, ymm12
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm2, ymm2, ymm11
	vpsubw ymm14, ymm10, ymm2
	vpaddw ymm10, ymm10, ymm2
	vpunpcklqdq ymm6, ymm13, ymm0
	vpunpckhqdq ymm0, ymm13, ymm0
	vpunpcklqdq ymm3, ymm1, ymm8
	vpunpckhqdq ymm8, ymm1, ymm8
	vpunpcklqdq ymm9, ymm4, ymm7
	vpunpckhqdq ymm7, ymm4, ymm7
	vpunpcklqdq ymm11, ymm10, ymm14
	vpunpckhqdq ymm14, ymm10, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+832]
	vmovdqu ymm12, YMMWORD PTR [r8+864]
	vpmullw ymm5, ymm0, ymm12
	vpmulhw ymm0, ymm0, ymm2
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm0, ymm0, ymm5
	vpsubw ymm13, ymm6, ymm0
	vpaddw ymm6, ymm6, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+896]
	vmovdqu ymm4, YMMWORD PTR [r8+928]
	vpmullw ymm10, ymm8, ymm4
	vpmulhw ymm8, ymm8, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm8, ymm8, ymm10
	vpsubw ymm5, ymm3, ymm8
	vpaddw ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [r8+960]
	vmovdqu ymm2, YMMWORD PTR [r8+992]
	vpmullw ymm12, ymm7, ymm2
	vpmulhw ymm7, ymm7, ymm0
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm7, ymm7, ymm12
	vpsubw ymm10, ymm9, ymm7
	vpaddw ymm9, ymm9, ymm7
	vmovdqu ymm8, YMMWORD PTR [r8+1024]
	vmovdqu ymm1, YMMWORD PTR [r8+1056]
	vpmullw ymm4, ymm14, ymm1
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm14, ymm14, ymm4
	vpsubw ymm12, ymm11, ymm14
	vpaddw ymm11, ymm11, ymm14
	vpsllq ymm7, ymm13, 32
	vpblendd ymm7, ymm6, ymm7, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm13, ymm6, ymm13, 170
	vpsllq ymm0, ymm5, 32
	vpblendd ymm0, ymm3, ymm0, 170
	vpsrlq ymm3, ymm3, 32
	vpblendd ymm5, ymm3, ymm5, 170
	vpsllq ymm2, ymm10, 32
	vpblendd ymm2, ymm9, ymm2, 170
	vpsrlq ymm9, ymm9, 32
	vpblendd ymm10, ymm9, ymm10, 170
	vpsllq ymm4, ymm12, 32
	vpblendd ymm4, ymm11, ymm4, 170
	vpsrlq ymm11, ymm11, 32
	vpblendd ymm12, ymm11, ymm12, 170
	vmovdqu ymm14, YMMWORD PTR [r8+1088]
	vmovdqu ymm8, YMMWORD PTR [r8+1120]
	vpmullw ymm1, ymm13, ymm8
	vpmulhw ymm13, ymm13, ymm14
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm13, ymm13, ymm1
	vpsubw ymm6, ymm7, ymm13
	vpaddw ymm7, ymm7, ymm13
	vmovdqu ymm3, YMMWORD PTR [r8+1152]
	vmovdqu ymm9, YMMWORD PTR [r8+1184]
	vpmullw ymm11, ymm5, ymm9
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm5, ymm5, ymm11
	vpsubw ymm1, ymm0, ymm5
	vpaddw ymm0, ymm0, ymm5
	vmovdqu ymm13, YMMWORD PTR [r8+1216]
	vmovdqu ymm14, YMMWORD PTR [r8+1248]
	vpmullw ymm8, ymm10, ymm14
	vpmulhw ymm10, ymm10, ymm13
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm10, ymm10, ymm8
	vpsubw ymm11, ymm2, ymm10
	vpaddw ymm2, ymm2, ymm10
	vmovdqu ymm5, YMMWORD PTR [r8+1280]
	vmovdqu ymm3, YMMWORD PTR [r8+1312]
	vpmullw ymm9, ymm12, ymm3
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm12, ymm12, ymm9
	vpsubw ymm8, ymm4, ymm12
	vpaddw ymm4, ymm4, ymm12
	vmovdqu ymm10, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm14, ymm7, ymm13
	vpmulhw ymm7, ymm7, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm7, ymm7, ymm14
	vpsraw ymm14, ymm7, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm7, ymm7, ymm14
	vpmullw ymm9, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm6, ymm6, ymm9
	vpsraw ymm9, ymm6, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm6, ymm6, ymm9
	vpmullw ymm12, ymm0, ymm13
	vpmulhw ymm0, ymm0, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm0, ymm0, ymm12
	vpsraw ymm12, ymm0, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm0, ymm0, ymm12
	vpmullw ymm5, ymm1, ymm13
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm1, ymm1, ymm5
	vpsraw ymm5, ymm1, 15
	vpand ymm5, ymm5, ymm15
	vpaddw ymm1, ymm1, ymm5
	vpmullw ymm3, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpsraw ymm3, ymm2, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm2, ymm2, ymm3
	vpmullw ymm14, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm11, ymm11, ymm14
	vpsraw ymm14, ymm11, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm11, ymm11, ymm14
	vpmullw ymm9, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm4, ymm4, ymm9
	vpsraw ymm9, ymm4, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm4, ymm4, ymm9
	vpmullw ymm12, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm8, ymm8, ymm12
	vpsraw ymm12, ymm8, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm8, ymm8, ymm12
	vpunpckldq ymm5, ymm7, ymm6
	vpunpckhdq ymm6, ymm7, ymm6
	vpunpckldq ymm3, ymm0, ymm1
	vpunpckhdq ymm1, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm11
	vpunpckhdq ymm11, ymm2, ymm11
	vpunpckldq ymm9, ymm4, ymm8
	vpunpckhdq ymm8, ymm4, ymm8
	vpxor ymm12, ymm12, ymm12
	vpermq ymm5, ymm5, 216
	vpunpckhwd ymm10, ymm5, ymm12
	vpunpcklwd ymm5, ymm5, ymm12
	vmovdqu YMMWORD PTR [r10], ymm5
	vmovdqu YMMWORD PTR [r10+64], ymm10
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm10, ymm6, ymm12
	vpunpcklwd ymm6, ymm6, ymm12
	vmovdqu YMMWORD PTR [r10+32], ymm6
	vmovdqu YMMWORD PTR [r10+96], ymm10
	vpermq ymm3, ymm3, 216
	vpunpckhwd ymm13, ymm3, ymm12
	vpunpcklwd ymm3, ymm3, ymm12
	vmovdqu YMMWORD PTR [r10+128], ymm3
	vmovdqu YMMWORD PTR [r10+192], ymm13
	vpermq ymm1, ymm1, 216
	vpunpckhwd ymm13, ymm1, ymm12
	vpunpcklwd ymm1, ymm1, ymm12
	vmovdqu YMMWORD PTR [r10+160], ymm1
	vmovdqu YMMWORD PTR [r10+224], ymm13
	vpermq ymm14, ymm14, 216
	vpunpckhwd ymm7, ymm14, ymm12
	vpunpcklwd ymm14, ymm14, ymm12
	vmovdqu YMMWORD PTR [r10+256], ymm14
	vmovdqu YMMWORD PTR [r10+320], ymm7
	vpermq ymm11, ymm11, 216
	vpunpckhwd ymm7, ymm11, ymm12
	vpunpcklwd ymm11, ymm11, ymm12
	vmovdqu YMMWORD PTR [r10+288], ymm11
	vmovdqu YMMWORD PTR [r10+352], ymm7
	vpermq ymm9, ymm9, 216
	vpunpckhwd ymm0, ymm9, ymm12
	vpunpcklwd ymm9, ymm9, ymm12
	vmovdqu YMMWORD PTR [r10+384], ymm9
	vmovdqu YMMWORD PTR [r10+448], ymm0
	vpermq ymm8, ymm8, 216
	vpunpckhwd ymm0, ymm8, ymm12
	vpunpcklwd ymm8, ymm8, ymm12
	vmovdqu YMMWORD PTR [r10+416], ymm8
	vmovdqu YMMWORD PTR [r10+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu ymm2, YMMWORD PTR [rsi+576]
	vmovdqu ymm3, YMMWORD PTR [rsi+608]
	vmovdqu ymm4, YMMWORD PTR [rsi+640]
	vmovdqu ymm5, YMMWORD PTR [rsi+672]
	vmovdqu ymm6, YMMWORD PTR [rsi+704]
	vmovdqu ymm7, YMMWORD PTR [rsi+736]
	vmovdqu ymm8, YMMWORD PTR [r8+1344]
	vmovdqu ymm9, YMMWORD PTR [r8+1376]
	vpmullw ymm10, ymm4, ymm9
	vpmullw ymm12, ymm5, ymm9
	vpmulhw ymm4, ymm4, ymm8
	vpmulhw ymm5, ymm5, ymm8
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm10
	vpsubw ymm5, ymm5, ymm12
	vpsubw ymm11, ymm0, ymm4
	vpsubw ymm13, ymm1, ymm5
	vpaddw ymm0, ymm0, ymm4
	vpaddw ymm1, ymm1, ymm5
	vmovdqu ymm14, YMMWORD PTR [r8+1344]
	vmovdqu ymm10, YMMWORD PTR [r8+1376]
	vpmullw ymm4, ymm6, ymm10
	vpmullw ymm5, ymm7, ymm10
	vpmulhw ymm6, ymm6, ymm14
	vpmulhw ymm7, ymm7, ymm14
	vpmulhw ymm4, ymm4, ymm15
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm6, ymm6, ymm4
	vpsubw ymm7, ymm7, ymm5
	vpsubw ymm12, ymm2, ymm6
	vpsubw ymm8, ymm3, ymm7
	vpaddw ymm2, ymm2, ymm6
	vpaddw ymm3, ymm3, ymm7
	vmovdqu ymm9, YMMWORD PTR [r8+1408]
	vmovdqu ymm4, YMMWORD PTR [r8+1440]
	vpmullw ymm6, ymm2, ymm4
	vpmullw ymm7, ymm3, ymm4
	vpmulhw ymm2, ymm2, ymm9
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm6, ymm6, ymm15
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm2, ymm2, ymm6
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm5, ymm0, ymm2
	vpsubw ymm14, ymm1, ymm3
	vpaddw ymm0, ymm0, ymm2
	vpaddw ymm1, ymm1, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+1472]
	vmovdqu ymm6, YMMWORD PTR [r8+1504]
	vpmullw ymm2, ymm12, ymm6
	vpmullw ymm3, ymm8, ymm6
	vpmulhw ymm12, ymm12, ymm10
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm2
	vpsubw ymm8, ymm8, ymm3
	vpsubw ymm7, ymm11, ymm12
	vpsubw ymm9, ymm13, ymm8
	vpaddw ymm11, ymm11, ymm12
	vpaddw ymm13, ymm13, ymm8
	vmovdqu ymm4, YMMWORD PTR [r8+1536]
	vmovdqu ymm2, YMMWORD PTR [r8+1568]
	vpmullw ymm12, ymm1, ymm2
	vpmulhw ymm1, ymm1, ymm4
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm1, ymm1, ymm12
	vpsubw ymm3, ymm0, ymm1
	vpaddw ymm0, ymm0, ymm1
	vmovdqu ymm8, YMMWORD PTR [r8+1600]
	vmovdqu ymm10, YMMWORD PTR [r8+1632]
	vpmullw ymm6, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vpsubw ymm12, ymm5, ymm14
	vpaddw ymm5, ymm5, ymm14
	vmovdqu ymm1, YMMWORD PTR [r8+1664]
	vmovdqu ymm4, YMMWORD PTR [r8+1696]
	vpmullw ymm2, ymm13, ymm4
	vpmulhw ymm13, ymm13, ymm1
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm13, ymm13, ymm2
	vpsubw ymm6, ymm11, ymm13
	vpaddw ymm11, ymm11, ymm13
	vmovdqu ymm14, YMMWORD PTR [r8+1728]
	vmovdqu ymm8, YMMWORD PTR [r8+1760]
	vpmullw ymm10, ymm9, ymm8
	vpmulhw ymm9, ymm9, ymm14
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm9, ymm9, ymm10
	vpsubw ymm2, ymm7, ymm9
	vpaddw ymm7, ymm7, ymm9
	vperm2i128 ymm13, ymm0, ymm3, 32
	vperm2i128 ymm3, ymm0, ymm3, 49
	vperm2i128 ymm1, ymm5, ymm12, 32
	vperm2i128 ymm12, ymm5, ymm12, 49
	vperm2i128 ymm4, ymm11, ymm6, 32
	vperm2i128 ymm6, ymm11, ymm6, 49
	vperm2i128 ymm10, ymm7, ymm2, 32
	vperm2i128 ymm2, ymm7, ymm2, 49
	vmovdqu ymm9, YMMWORD PTR [r8+1792]
	vmovdqu ymm14, YMMWORD PTR [r8+1824]
	vpmullw ymm8, ymm3, ymm14
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm3, ymm3, ymm8
	vpsubw ymm0, ymm13, ymm3
	vpaddw ymm13, ymm13, ymm3
	vmovdqu ymm5, YMMWORD PTR [r8+1856]
	vmovdqu ymm11, YMMWORD PTR [r8+1888]
	vpmullw ymm7, ymm12, ymm11
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm12, ymm12, ymm7
	vpsubw ymm8, ymm1, ymm12
	vpaddw ymm1, ymm1, ymm12
	vmovdqu ymm3, YMMWORD PTR [r8+1920]
	vmovdqu ymm9, YMMWORD PTR [r8+1952]
	vpmullw ymm14, ymm6, ymm9
	vpmulhw ymm6, ymm6, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm6, ymm6, ymm14
	vpsubw ymm7, ymm4, ymm6
	vpaddw ymm4, ymm4, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+1984]
	vmovdqu ymm5, YMMWORD PTR [r8+2016]
	vpmullw ymm11, ymm2, ymm5
	vpmulhw ymm2, ymm2, ymm12
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm2, ymm2, ymm11
	vpsubw ymm14, ymm10, ymm2
	vpaddw ymm10, ymm10, ymm2
	vpunpcklqdq ymm6, ymm13, ymm0
	vpunpckhqdq ymm0, ymm13, ymm0
	vpunpcklqdq ymm3, ymm1, ymm8
	vpunpckhqdq ymm8, ymm1, ymm8
	vpunpcklqdq ymm9, ymm4, ymm7
	vpunpckhqdq ymm7, ymm4, ymm7
	vpunpcklqdq ymm11, ymm10, ymm14
	vpunpckhqdq ymm14, ymm10, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+2048]
	vmovdqu ymm12, YMMWORD PTR [r8+2080]
	vpmullw ymm5, ymm0, ymm12
	vpmulhw ymm0, ymm0, ymm2
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm0, ymm0, ymm5
	vpsubw ymm13, ymm6, ymm0
	vpaddw ymm6, ymm6, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+2112]
	vmovdqu ymm4, YMMWORD PTR [r8+2144]
	vpmullw ymm10, ymm8, ymm4
	vpmulhw ymm8, ymm8, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm8, ymm8, ymm10
	vpsubw ymm5, ymm3, ymm8
	vpaddw ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [r8+2176]
	vmovdqu ymm2, YMMWORD PTR [r8+2208]
	vpmullw ymm12, ymm7, ymm2
	vpmulhw ymm7, ymm7, ymm0
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm7, ymm7, ymm12
	vpsubw ymm10, ymm9, ymm7
	vpaddw ymm9, ymm9, ymm7
	vmovdqu ymm8, YMMWORD PTR [r8+2240]
	vmovdqu ymm1, YMMWORD PTR [r8+2272]
	vpmullw ymm4, ymm14, ymm1
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm14, ymm14, ymm4
	vpsubw ymm12, ymm11, ymm14
	vpaddw ymm11, ymm11, ymm14
	vpsllq ymm7, ymm13, 32
	vpblendd ymm7, ymm6, ymm7, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm13, ymm6, ymm13, 170
	vpsllq ymm0, ymm5, 32
	vpblendd ymm0, ymm3, ymm0, 170
	vpsrlq ymm3, ymm3, 32
	vpblendd ymm5, ymm3, ymm5, 170
	vpsllq ymm2, ymm10, 32
	vpblendd ymm2, ymm9, ymm2, 170
	vpsrlq ymm9, ymm9, 32
	vpblendd ymm10, ymm9, ymm10, 170
	vpsllq ymm4, ymm12, 32
	vpblendd ymm4, ymm11, ymm4, 170
	vpsrlq ymm11, ymm11, 32
	vpblendd ymm12, ymm11, ymm12, 170
	vmovdqu ymm14, YMMWORD PTR [r8+2304]
	vmovdqu ymm8, YMMWORD PTR [r8+2336]
	vpmullw ymm1, ymm13, ymm8
	vpmulhw ymm13, ymm13, ymm14
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm13, ymm13, ymm1
	vpsubw ymm6, ymm7, ymm13
	vpaddw ymm7, ymm7, ymm13
	vmovdqu ymm3, YMMWORD PTR [r8+2368]
	vmovdqu ymm9, YMMWORD PTR [r8+2400]
	vpmullw ymm11, ymm5, ymm9
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm5, ymm5, ymm11
	vpsubw ymm1, ymm0, ymm5
	vpaddw ymm0, ymm0, ymm5
	vmovdqu ymm13, YMMWORD PTR [r8+2432]
	vmovdqu ymm14, YMMWORD PTR [r8+2464]
	vpmullw ymm8, ymm10, ymm14
	vpmulhw ymm10, ymm10, ymm13
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm10, ymm10, ymm8
	vpsubw ymm11, ymm2, ymm10
	vpaddw ymm2, ymm2, ymm10
	vmovdqu ymm5, YMMWORD PTR [r8+2496]
	vmovdqu ymm3, YMMWORD PTR [r8+2528]
	vpmullw ymm9, ymm12, ymm3
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm12, ymm12, ymm9
	vpsubw ymm8, ymm4, ymm12
	vpaddw ymm4, ymm4, ymm12
	vmovdqu ymm10, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm14, ymm7, ymm13
	vpmulhw ymm7, ymm7, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm7, ymm7, ymm14
	vpsraw ymm14, ymm7, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm7, ymm7, ymm14
	vpmullw ymm9, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm6, ymm6, ymm9
	vpsraw ymm9, ymm6, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm6, ymm6, ymm9
	vpmullw ymm12, ymm0, ymm13
	vpmulhw ymm0, ymm0, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm0, ymm0, ymm12
	vpsraw ymm12, ymm0, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm0, ymm0, ymm12
	vpmullw ymm5, ymm1, ymm13
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm1, ymm1, ymm5
	vpsraw ymm5, ymm1, 15
	vpand ymm5, ymm5, ymm15
	vpaddw ymm1, ymm1, ymm5
	vpmullw ymm3, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpsraw ymm3, ymm2, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm2, ymm2, ymm3
	vpmullw ymm14, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm11, ymm11, ymm14
	vpsraw ymm14, ymm11, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm11, ymm11, ymm14
	vpmullw ymm9, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm4, ymm4, ymm9
	vpsraw ymm9, ymm4, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm4, ymm4, ymm9
	vpmullw ymm12, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm8, ymm8, ymm12
	vpsraw ymm12, ymm8, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm8, ymm8, ymm12
	vpunpckldq ymm5, ymm7, ymm6
	vpunpckhdq ymm6, ymm7, ymm6
	vpunpckldq ymm3, ymm0, ymm1
	vpunpckhdq ymm1, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm11
	vpunpckhdq ymm11, ymm2, ymm11
	vpunpckldq ymm9, ymm4, ymm8
	vpunpckhdq ymm8, ymm4, ymm8
	vpxor ymm12, ymm12, ymm12
	vpermq ymm5, ymm5, 216
	vpunpckhwd ymm10, ymm5, ymm12
	vpunpcklwd ymm5, ymm5, ymm12
	vmovdqu YMMWORD PTR [r10+512], ymm5
	vmovdqu YMMWORD PTR [r10+576], ymm10
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm10, ymm6, ymm12
	vpunpcklwd ymm6, ymm6, ymm12
	vmovdqu YMMWORD PTR [r10+544], ymm6
	vmovdqu YMMWORD PTR [r10+608], ymm10
	vpermq ymm3, ymm3, 216
	vpunpckhwd ymm13, ymm3, ymm12
	vpunpcklwd ymm3, ymm3, ymm12
	vmovdqu YMMWORD PTR [r10+640], ymm3
	vmovdqu YMMWORD PTR [r10+704], ymm13
	vpermq ymm1, ymm1, 216
	vpunpckhwd ymm13, ymm1, ymm12
	vpunpcklwd ymm1, ymm1, ymm12
	vmovdqu YMMWORD PTR [r10+672], ymm1
	vmovdqu YMMWORD PTR [r10+736], ymm13
	vpermq ymm14, ymm14, 216
	vpunpckhwd ymm7, ymm14, ymm12
	vpunpcklwd ymm14, ymm14, ymm12
	vmovdqu YMMWORD PTR [r10+768], ymm14
	vmovdqu YMMWORD PTR [r10+832], ymm7
	vpermq ymm11, ymm11, 216
	vpunpckhwd ymm7, ymm11, ymm12
	vpunpcklwd ymm11, ymm11, ymm12
	vmovdqu YMMWORD PTR [r10+800], ymm11
	vmovdqu YMMWORD PTR [r10+864], ymm7
	vpermq ymm9, ymm9, 216
	vpunpckhwd ymm0, ymm9, ymm12
	vpunpcklwd ymm9, ymm9, ymm12
	vmovdqu YMMWORD PTR [r10+896], ymm9
	vmovdqu YMMWORD PTR [r10+960], ymm0
	vpermq ymm8, ymm8, 216
	vpunpckhwd ymm0, ymm8, ymm12
	vpunpcklwd ymm8, ymm8, ymm12
	vmovdqu YMMWORD PTR [r10+928], ymm8
	vmovdqu YMMWORD PTR [r10+992], ymm0
	vzeroupper
	mov rdi, r15
	mov rsi, rbx
	mov r10, rbp
	mov eax, 218172673
	vmovq xmm15, rax
	vpbroadcastd ymm15, xmm15
	lea r8, {VG_MLKEM_NTT_ZETAS}
	vmovdqu ymm12, YMMWORD PTR [r8+64]
	vmovdqu ymm13, YMMWORD PTR [r8+96]
	vmovdqu ymm4, YMMWORD PTR [rdi]
	vmovdqu ymm5, YMMWORD PTR [rdi+256]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+256], ymm4
	vmovdqu YMMWORD PTR [rsi+512], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+32]
	vmovdqu ymm5, YMMWORD PTR [rdi+288]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+288], ymm4
	vmovdqu YMMWORD PTR [rsi+544], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+64]
	vmovdqu ymm5, YMMWORD PTR [rdi+320]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+320], ymm4
	vmovdqu YMMWORD PTR [rsi+576], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+96]
	vmovdqu ymm5, YMMWORD PTR [rdi+352]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+352], ymm4
	vmovdqu YMMWORD PTR [rsi+608], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+128]
	vmovdqu ymm5, YMMWORD PTR [rdi+384]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+384], ymm4
	vmovdqu YMMWORD PTR [rsi+640], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+160]
	vmovdqu ymm5, YMMWORD PTR [rdi+416]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+416], ymm4
	vmovdqu YMMWORD PTR [rsi+672], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+192]
	vmovdqu ymm5, YMMWORD PTR [rdi+448]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+448], ymm4
	vmovdqu YMMWORD PTR [rsi+704], ymm6
	vmovdqu ymm4, YMMWORD PTR [rdi+224]
	vmovdqu ymm5, YMMWORD PTR [rdi+480]
	vpmullw ymm2, ymm5, ymm13
	vpmulhw ymm5, ymm5, ymm12
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm5, ymm5, ymm2
	vpsubw ymm6, ymm4, ymm5
	vpaddw ymm4, ymm4, ymm5
	vmovdqu YMMWORD PTR [rsi+480], ymm4
	vmovdqu YMMWORD PTR [rsi+736], ymm6
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu ymm2, YMMWORD PTR [rsi+320]
	vmovdqu ymm3, YMMWORD PTR [rsi+352]
	vmovdqu ymm4, YMMWORD PTR [rsi+384]
	vmovdqu ymm5, YMMWORD PTR [rsi+416]
	vmovdqu ymm6, YMMWORD PTR [rsi+448]
	vmovdqu ymm7, YMMWORD PTR [rsi+480]
	vmovdqu ymm8, YMMWORD PTR [r8+128]
	vmovdqu ymm9, YMMWORD PTR [r8+160]
	vpmullw ymm10, ymm4, ymm9
	vpmullw ymm12, ymm5, ymm9
	vpmulhw ymm4, ymm4, ymm8
	vpmulhw ymm5, ymm5, ymm8
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm10
	vpsubw ymm5, ymm5, ymm12
	vpsubw ymm11, ymm0, ymm4
	vpsubw ymm13, ymm1, ymm5
	vpaddw ymm0, ymm0, ymm4
	vpaddw ymm1, ymm1, ymm5
	vmovdqu ymm14, YMMWORD PTR [r8+128]
	vmovdqu ymm10, YMMWORD PTR [r8+160]
	vpmullw ymm4, ymm6, ymm10
	vpmullw ymm5, ymm7, ymm10
	vpmulhw ymm6, ymm6, ymm14
	vpmulhw ymm7, ymm7, ymm14
	vpmulhw ymm4, ymm4, ymm15
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm6, ymm6, ymm4
	vpsubw ymm7, ymm7, ymm5
	vpsubw ymm12, ymm2, ymm6
	vpsubw ymm8, ymm3, ymm7
	vpaddw ymm2, ymm2, ymm6
	vpaddw ymm3, ymm3, ymm7
	vmovdqu ymm9, YMMWORD PTR [r8+192]
	vmovdqu ymm4, YMMWORD PTR [r8+224]
	vpmullw ymm6, ymm2, ymm4
	vpmullw ymm7, ymm3, ymm4
	vpmulhw ymm2, ymm2, ymm9
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm6, ymm6, ymm15
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm2, ymm2, ymm6
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm5, ymm0, ymm2
	vpsubw ymm14, ymm1, ymm3
	vpaddw ymm0, ymm0, ymm2
	vpaddw ymm1, ymm1, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+256]
	vmovdqu ymm6, YMMWORD PTR [r8+288]
	vpmullw ymm2, ymm12, ymm6
	vpmullw ymm3, ymm8, ymm6
	vpmulhw ymm12, ymm12, ymm10
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm2
	vpsubw ymm8, ymm8, ymm3
	vpsubw ymm7, ymm11, ymm12
	vpsubw ymm9, ymm13, ymm8
	vpaddw ymm11, ymm11, ymm12
	vpaddw ymm13, ymm13, ymm8
	vmovdqu ymm4, YMMWORD PTR [r8+320]
	vmovdqu ymm2, YMMWORD PTR [r8+352]
	vpmullw ymm12, ymm1, ymm2
	vpmulhw ymm1, ymm1, ymm4
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm1, ymm1, ymm12
	vpsubw ymm3, ymm0, ymm1
	vpaddw ymm0, ymm0, ymm1
	vmovdqu ymm8, YMMWORD PTR [r8+384]
	vmovdqu ymm10, YMMWORD PTR [r8+416]
	vpmullw ymm6, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vpsubw ymm12, ymm5, ymm14
	vpaddw ymm5, ymm5, ymm14
	vmovdqu ymm1, YMMWORD PTR [r8+448]
	vmovdqu ymm4, YMMWORD PTR [r8+480]
	vpmullw ymm2, ymm13, ymm4
	vpmulhw ymm13, ymm13, ymm1
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm13, ymm13, ymm2
	vpsubw ymm6, ymm11, ymm13
	vpaddw ymm11, ymm11, ymm13
	vmovdqu ymm14, YMMWORD PTR [r8+512]
	vmovdqu ymm8, YMMWORD PTR [r8+544]
	vpmullw ymm10, ymm9, ymm8
	vpmulhw ymm9, ymm9, ymm14
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm9, ymm9, ymm10
	vpsubw ymm2, ymm7, ymm9
	vpaddw ymm7, ymm7, ymm9
	vperm2i128 ymm13, ymm0, ymm3, 32
	vperm2i128 ymm3, ymm0, ymm3, 49
	vperm2i128 ymm1, ymm5, ymm12, 32
	vperm2i128 ymm12, ymm5, ymm12, 49
	vperm2i128 ymm4, ymm11, ymm6, 32
	vperm2i128 ymm6, ymm11, ymm6, 49
	vperm2i128 ymm10, ymm7, ymm2, 32
	vperm2i128 ymm2, ymm7, ymm2, 49
	vmovdqu ymm9, YMMWORD PTR [r8+576]
	vmovdqu ymm14, YMMWORD PTR [r8+608]
	vpmullw ymm8, ymm3, ymm14
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm3, ymm3, ymm8
	vpsubw ymm0, ymm13, ymm3
	vpaddw ymm13, ymm13, ymm3
	vmovdqu ymm5, YMMWORD PTR [r8+640]
	vmovdqu ymm11, YMMWORD PTR [r8+672]
	vpmullw ymm7, ymm12, ymm11
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm12, ymm12, ymm7
	vpsubw ymm8, ymm1, ymm12
	vpaddw ymm1, ymm1, ymm12
	vmovdqu ymm3, YMMWORD PTR [r8+704]
	vmovdqu ymm9, YMMWORD PTR [r8+736]
	vpmullw ymm14, ymm6, ymm9
	vpmulhw ymm6, ymm6, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm6, ymm6, ymm14
	vpsubw ymm7, ymm4, ymm6
	vpaddw ymm4, ymm4, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+768]
	vmovdqu ymm5, YMMWORD PTR [r8+800]
	vpmullw ymm11, ymm2, ymm5
	vpmulhw ymm2, ymm2, ymm12
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm2, ymm2, ymm11
	vpsubw ymm14, ymm10, ymm2
	vpaddw ymm10, ymm10, ymm2
	vpunpcklqdq ymm6, ymm13, ymm0
	vpunpckhqdq ymm0, ymm13, ymm0
	vpunpcklqdq ymm3, ymm1, ymm8
	vpunpckhqdq ymm8, ymm1, ymm8
	vpunpcklqdq ymm9, ymm4, ymm7
	vpunpckhqdq ymm7, ymm4, ymm7
	vpunpcklqdq ymm11, ymm10, ymm14
	vpunpckhqdq ymm14, ymm10, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+832]
	vmovdqu ymm12, YMMWORD PTR [r8+864]
	vpmullw ymm5, ymm0, ymm12
	vpmulhw ymm0, ymm0, ymm2
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm0, ymm0, ymm5
	vpsubw ymm13, ymm6, ymm0
	vpaddw ymm6, ymm6, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+896]
	vmovdqu ymm4, YMMWORD PTR [r8+928]
	vpmullw ymm10, ymm8, ymm4
	vpmulhw ymm8, ymm8, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm8, ymm8, ymm10
	vpsubw ymm5, ymm3, ymm8
	vpaddw ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [r8+960]
	vmovdqu ymm2, YMMWORD PTR [r8+992]
	vpmullw ymm12, ymm7, ymm2
	vpmulhw ymm7, ymm7, ymm0
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm7, ymm7, ymm12
	vpsubw ymm10, ymm9, ymm7
	vpaddw ymm9, ymm9, ymm7
	vmovdqu ymm8, YMMWORD PTR [r8+1024]
	vmovdqu ymm1, YMMWORD PTR [r8+1056]
	vpmullw ymm4, ymm14, ymm1
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm14, ymm14, ymm4
	vpsubw ymm12, ymm11, ymm14
	vpaddw ymm11, ymm11, ymm14
	vpsllq ymm7, ymm13, 32
	vpblendd ymm7, ymm6, ymm7, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm13, ymm6, ymm13, 170
	vpsllq ymm0, ymm5, 32
	vpblendd ymm0, ymm3, ymm0, 170
	vpsrlq ymm3, ymm3, 32
	vpblendd ymm5, ymm3, ymm5, 170
	vpsllq ymm2, ymm10, 32
	vpblendd ymm2, ymm9, ymm2, 170
	vpsrlq ymm9, ymm9, 32
	vpblendd ymm10, ymm9, ymm10, 170
	vpsllq ymm4, ymm12, 32
	vpblendd ymm4, ymm11, ymm4, 170
	vpsrlq ymm11, ymm11, 32
	vpblendd ymm12, ymm11, ymm12, 170
	vmovdqu ymm14, YMMWORD PTR [r8+1088]
	vmovdqu ymm8, YMMWORD PTR [r8+1120]
	vpmullw ymm1, ymm13, ymm8
	vpmulhw ymm13, ymm13, ymm14
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm13, ymm13, ymm1
	vpsubw ymm6, ymm7, ymm13
	vpaddw ymm7, ymm7, ymm13
	vmovdqu ymm3, YMMWORD PTR [r8+1152]
	vmovdqu ymm9, YMMWORD PTR [r8+1184]
	vpmullw ymm11, ymm5, ymm9
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm5, ymm5, ymm11
	vpsubw ymm1, ymm0, ymm5
	vpaddw ymm0, ymm0, ymm5
	vmovdqu ymm13, YMMWORD PTR [r8+1216]
	vmovdqu ymm14, YMMWORD PTR [r8+1248]
	vpmullw ymm8, ymm10, ymm14
	vpmulhw ymm10, ymm10, ymm13
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm10, ymm10, ymm8
	vpsubw ymm11, ymm2, ymm10
	vpaddw ymm2, ymm2, ymm10
	vmovdqu ymm5, YMMWORD PTR [r8+1280]
	vmovdqu ymm3, YMMWORD PTR [r8+1312]
	vpmullw ymm9, ymm12, ymm3
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm12, ymm12, ymm9
	vpsubw ymm8, ymm4, ymm12
	vpaddw ymm4, ymm4, ymm12
	vmovdqu ymm10, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm14, ymm7, ymm13
	vpmulhw ymm7, ymm7, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm7, ymm7, ymm14
	vpsraw ymm14, ymm7, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm7, ymm7, ymm14
	vpmullw ymm9, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm6, ymm6, ymm9
	vpsraw ymm9, ymm6, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm6, ymm6, ymm9
	vpmullw ymm12, ymm0, ymm13
	vpmulhw ymm0, ymm0, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm0, ymm0, ymm12
	vpsraw ymm12, ymm0, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm0, ymm0, ymm12
	vpmullw ymm5, ymm1, ymm13
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm1, ymm1, ymm5
	vpsraw ymm5, ymm1, 15
	vpand ymm5, ymm5, ymm15
	vpaddw ymm1, ymm1, ymm5
	vpmullw ymm3, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpsraw ymm3, ymm2, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm2, ymm2, ymm3
	vpmullw ymm14, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm11, ymm11, ymm14
	vpsraw ymm14, ymm11, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm11, ymm11, ymm14
	vpmullw ymm9, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm4, ymm4, ymm9
	vpsraw ymm9, ymm4, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm4, ymm4, ymm9
	vpmullw ymm12, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm8, ymm8, ymm12
	vpsraw ymm12, ymm8, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm8, ymm8, ymm12
	vpunpckldq ymm5, ymm7, ymm6
	vpunpckhdq ymm6, ymm7, ymm6
	vpunpckldq ymm3, ymm0, ymm1
	vpunpckhdq ymm1, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm11
	vpunpckhdq ymm11, ymm2, ymm11
	vpunpckldq ymm9, ymm4, ymm8
	vpunpckhdq ymm8, ymm4, ymm8
	vpxor ymm12, ymm12, ymm12
	vpermq ymm5, ymm5, 216
	vpunpckhwd ymm10, ymm5, ymm12
	vpunpcklwd ymm5, ymm5, ymm12
	vmovdqu YMMWORD PTR [r10], ymm5
	vmovdqu YMMWORD PTR [r10+64], ymm10
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm10, ymm6, ymm12
	vpunpcklwd ymm6, ymm6, ymm12
	vmovdqu YMMWORD PTR [r10+32], ymm6
	vmovdqu YMMWORD PTR [r10+96], ymm10
	vpermq ymm3, ymm3, 216
	vpunpckhwd ymm13, ymm3, ymm12
	vpunpcklwd ymm3, ymm3, ymm12
	vmovdqu YMMWORD PTR [r10+128], ymm3
	vmovdqu YMMWORD PTR [r10+192], ymm13
	vpermq ymm1, ymm1, 216
	vpunpckhwd ymm13, ymm1, ymm12
	vpunpcklwd ymm1, ymm1, ymm12
	vmovdqu YMMWORD PTR [r10+160], ymm1
	vmovdqu YMMWORD PTR [r10+224], ymm13
	vpermq ymm14, ymm14, 216
	vpunpckhwd ymm7, ymm14, ymm12
	vpunpcklwd ymm14, ymm14, ymm12
	vmovdqu YMMWORD PTR [r10+256], ymm14
	vmovdqu YMMWORD PTR [r10+320], ymm7
	vpermq ymm11, ymm11, 216
	vpunpckhwd ymm7, ymm11, ymm12
	vpunpcklwd ymm11, ymm11, ymm12
	vmovdqu YMMWORD PTR [r10+288], ymm11
	vmovdqu YMMWORD PTR [r10+352], ymm7
	vpermq ymm9, ymm9, 216
	vpunpckhwd ymm0, ymm9, ymm12
	vpunpcklwd ymm9, ymm9, ymm12
	vmovdqu YMMWORD PTR [r10+384], ymm9
	vmovdqu YMMWORD PTR [r10+448], ymm0
	vpermq ymm8, ymm8, 216
	vpunpckhwd ymm0, ymm8, ymm12
	vpunpcklwd ymm8, ymm8, ymm12
	vmovdqu YMMWORD PTR [r10+416], ymm8
	vmovdqu YMMWORD PTR [r10+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu ymm2, YMMWORD PTR [rsi+576]
	vmovdqu ymm3, YMMWORD PTR [rsi+608]
	vmovdqu ymm4, YMMWORD PTR [rsi+640]
	vmovdqu ymm5, YMMWORD PTR [rsi+672]
	vmovdqu ymm6, YMMWORD PTR [rsi+704]
	vmovdqu ymm7, YMMWORD PTR [rsi+736]
	vmovdqu ymm8, YMMWORD PTR [r8+1344]
	vmovdqu ymm9, YMMWORD PTR [r8+1376]
	vpmullw ymm10, ymm4, ymm9
	vpmullw ymm12, ymm5, ymm9
	vpmulhw ymm4, ymm4, ymm8
	vpmulhw ymm5, ymm5, ymm8
	vpmulhw ymm10, ymm10, ymm15
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm4, ymm4, ymm10
	vpsubw ymm5, ymm5, ymm12
	vpsubw ymm11, ymm0, ymm4
	vpsubw ymm13, ymm1, ymm5
	vpaddw ymm0, ymm0, ymm4
	vpaddw ymm1, ymm1, ymm5
	vmovdqu ymm14, YMMWORD PTR [r8+1344]
	vmovdqu ymm10, YMMWORD PTR [r8+1376]
	vpmullw ymm4, ymm6, ymm10
	vpmullw ymm5, ymm7, ymm10
	vpmulhw ymm6, ymm6, ymm14
	vpmulhw ymm7, ymm7, ymm14
	vpmulhw ymm4, ymm4, ymm15
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm6, ymm6, ymm4
	vpsubw ymm7, ymm7, ymm5
	vpsubw ymm12, ymm2, ymm6
	vpsubw ymm8, ymm3, ymm7
	vpaddw ymm2, ymm2, ymm6
	vpaddw ymm3, ymm3, ymm7
	vmovdqu ymm9, YMMWORD PTR [r8+1408]
	vmovdqu ymm4, YMMWORD PTR [r8+1440]
	vpmullw ymm6, ymm2, ymm4
	vpmullw ymm7, ymm3, ymm4
	vpmulhw ymm2, ymm2, ymm9
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm6, ymm6, ymm15
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm2, ymm2, ymm6
	vpsubw ymm3, ymm3, ymm7
	vpsubw ymm5, ymm0, ymm2
	vpsubw ymm14, ymm1, ymm3
	vpaddw ymm0, ymm0, ymm2
	vpaddw ymm1, ymm1, ymm3
	vmovdqu ymm10, YMMWORD PTR [r8+1472]
	vmovdqu ymm6, YMMWORD PTR [r8+1504]
	vpmullw ymm2, ymm12, ymm6
	vpmullw ymm3, ymm8, ymm6
	vpmulhw ymm12, ymm12, ymm10
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm2, ymm2, ymm15
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm12, ymm12, ymm2
	vpsubw ymm8, ymm8, ymm3
	vpsubw ymm7, ymm11, ymm12
	vpsubw ymm9, ymm13, ymm8
	vpaddw ymm11, ymm11, ymm12
	vpaddw ymm13, ymm13, ymm8
	vmovdqu ymm4, YMMWORD PTR [r8+1536]
	vmovdqu ymm2, YMMWORD PTR [r8+1568]
	vpmullw ymm12, ymm1, ymm2
	vpmulhw ymm1, ymm1, ymm4
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm1, ymm1, ymm12
	vpsubw ymm3, ymm0, ymm1
	vpaddw ymm0, ymm0, ymm1
	vmovdqu ymm8, YMMWORD PTR [r8+1600]
	vmovdqu ymm10, YMMWORD PTR [r8+1632]
	vpmullw ymm6, ymm14, ymm10
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm6, ymm6, ymm15
	vpsubw ymm14, ymm14, ymm6
	vpsubw ymm12, ymm5, ymm14
	vpaddw ymm5, ymm5, ymm14
	vmovdqu ymm1, YMMWORD PTR [r8+1664]
	vmovdqu ymm4, YMMWORD PTR [r8+1696]
	vpmullw ymm2, ymm13, ymm4
	vpmulhw ymm13, ymm13, ymm1
	vpmulhw ymm2, ymm2, ymm15
	vpsubw ymm13, ymm13, ymm2
	vpsubw ymm6, ymm11, ymm13
	vpaddw ymm11, ymm11, ymm13
	vmovdqu ymm14, YMMWORD PTR [r8+1728]
	vmovdqu ymm8, YMMWORD PTR [r8+1760]
	vpmullw ymm10, ymm9, ymm8
	vpmulhw ymm9, ymm9, ymm14
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm9, ymm9, ymm10
	vpsubw ymm2, ymm7, ymm9
	vpaddw ymm7, ymm7, ymm9
	vperm2i128 ymm13, ymm0, ymm3, 32
	vperm2i128 ymm3, ymm0, ymm3, 49
	vperm2i128 ymm1, ymm5, ymm12, 32
	vperm2i128 ymm12, ymm5, ymm12, 49
	vperm2i128 ymm4, ymm11, ymm6, 32
	vperm2i128 ymm6, ymm11, ymm6, 49
	vperm2i128 ymm10, ymm7, ymm2, 32
	vperm2i128 ymm2, ymm7, ymm2, 49
	vmovdqu ymm9, YMMWORD PTR [r8+1792]
	vmovdqu ymm14, YMMWORD PTR [r8+1824]
	vpmullw ymm8, ymm3, ymm14
	vpmulhw ymm3, ymm3, ymm9
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm3, ymm3, ymm8
	vpsubw ymm0, ymm13, ymm3
	vpaddw ymm13, ymm13, ymm3
	vmovdqu ymm5, YMMWORD PTR [r8+1856]
	vmovdqu ymm11, YMMWORD PTR [r8+1888]
	vpmullw ymm7, ymm12, ymm11
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm7, ymm7, ymm15
	vpsubw ymm12, ymm12, ymm7
	vpsubw ymm8, ymm1, ymm12
	vpaddw ymm1, ymm1, ymm12
	vmovdqu ymm3, YMMWORD PTR [r8+1920]
	vmovdqu ymm9, YMMWORD PTR [r8+1952]
	vpmullw ymm14, ymm6, ymm9
	vpmulhw ymm6, ymm6, ymm3
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm6, ymm6, ymm14
	vpsubw ymm7, ymm4, ymm6
	vpaddw ymm4, ymm4, ymm6
	vmovdqu ymm12, YMMWORD PTR [r8+1984]
	vmovdqu ymm5, YMMWORD PTR [r8+2016]
	vpmullw ymm11, ymm2, ymm5
	vpmulhw ymm2, ymm2, ymm12
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm2, ymm2, ymm11
	vpsubw ymm14, ymm10, ymm2
	vpaddw ymm10, ymm10, ymm2
	vpunpcklqdq ymm6, ymm13, ymm0
	vpunpckhqdq ymm0, ymm13, ymm0
	vpunpcklqdq ymm3, ymm1, ymm8
	vpunpckhqdq ymm8, ymm1, ymm8
	vpunpcklqdq ymm9, ymm4, ymm7
	vpunpckhqdq ymm7, ymm4, ymm7
	vpunpcklqdq ymm11, ymm10, ymm14
	vpunpckhqdq ymm14, ymm10, ymm14
	vmovdqu ymm2, YMMWORD PTR [r8+2048]
	vmovdqu ymm12, YMMWORD PTR [r8+2080]
	vpmullw ymm5, ymm0, ymm12
	vpmulhw ymm0, ymm0, ymm2
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm0, ymm0, ymm5
	vpsubw ymm13, ymm6, ymm0
	vpaddw ymm6, ymm6, ymm0
	vmovdqu ymm1, YMMWORD PTR [r8+2112]
	vmovdqu ymm4, YMMWORD PTR [r8+2144]
	vpmullw ymm10, ymm8, ymm4
	vpmulhw ymm8, ymm8, ymm1
	vpmulhw ymm10, ymm10, ymm15
	vpsubw ymm8, ymm8, ymm10
	vpsubw ymm5, ymm3, ymm8
	vpaddw ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [r8+2176]
	vmovdqu ymm2, YMMWORD PTR [r8+2208]
	vpmullw ymm12, ymm7, ymm2
	vpmulhw ymm7, ymm7, ymm0
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm7, ymm7, ymm12
	vpsubw ymm10, ymm9, ymm7
	vpaddw ymm9, ymm9, ymm7
	vmovdqu ymm8, YMMWORD PTR [r8+2240]
	vmovdqu ymm1, YMMWORD PTR [r8+2272]
	vpmullw ymm4, ymm14, ymm1
	vpmulhw ymm14, ymm14, ymm8
	vpmulhw ymm4, ymm4, ymm15
	vpsubw ymm14, ymm14, ymm4
	vpsubw ymm12, ymm11, ymm14
	vpaddw ymm11, ymm11, ymm14
	vpsllq ymm7, ymm13, 32
	vpblendd ymm7, ymm6, ymm7, 170
	vpsrlq ymm6, ymm6, 32
	vpblendd ymm13, ymm6, ymm13, 170
	vpsllq ymm0, ymm5, 32
	vpblendd ymm0, ymm3, ymm0, 170
	vpsrlq ymm3, ymm3, 32
	vpblendd ymm5, ymm3, ymm5, 170
	vpsllq ymm2, ymm10, 32
	vpblendd ymm2, ymm9, ymm2, 170
	vpsrlq ymm9, ymm9, 32
	vpblendd ymm10, ymm9, ymm10, 170
	vpsllq ymm4, ymm12, 32
	vpblendd ymm4, ymm11, ymm4, 170
	vpsrlq ymm11, ymm11, 32
	vpblendd ymm12, ymm11, ymm12, 170
	vmovdqu ymm14, YMMWORD PTR [r8+2304]
	vmovdqu ymm8, YMMWORD PTR [r8+2336]
	vpmullw ymm1, ymm13, ymm8
	vpmulhw ymm13, ymm13, ymm14
	vpmulhw ymm1, ymm1, ymm15
	vpsubw ymm13, ymm13, ymm1
	vpsubw ymm6, ymm7, ymm13
	vpaddw ymm7, ymm7, ymm13
	vmovdqu ymm3, YMMWORD PTR [r8+2368]
	vmovdqu ymm9, YMMWORD PTR [r8+2400]
	vpmullw ymm11, ymm5, ymm9
	vpmulhw ymm5, ymm5, ymm3
	vpmulhw ymm11, ymm11, ymm15
	vpsubw ymm5, ymm5, ymm11
	vpsubw ymm1, ymm0, ymm5
	vpaddw ymm0, ymm0, ymm5
	vmovdqu ymm13, YMMWORD PTR [r8+2432]
	vmovdqu ymm14, YMMWORD PTR [r8+2464]
	vpmullw ymm8, ymm10, ymm14
	vpmulhw ymm10, ymm10, ymm13
	vpmulhw ymm8, ymm8, ymm15
	vpsubw ymm10, ymm10, ymm8
	vpsubw ymm11, ymm2, ymm10
	vpaddw ymm2, ymm2, ymm10
	vmovdqu ymm5, YMMWORD PTR [r8+2496]
	vmovdqu ymm3, YMMWORD PTR [r8+2528]
	vpmullw ymm9, ymm12, ymm3
	vpmulhw ymm12, ymm12, ymm5
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm12, ymm12, ymm9
	vpsubw ymm8, ymm4, ymm12
	vpaddw ymm4, ymm4, ymm12
	vmovdqu ymm10, YMMWORD PTR [r8]
	vmovdqu ymm13, YMMWORD PTR [r8+32]
	vpmullw ymm14, ymm7, ymm13
	vpmulhw ymm7, ymm7, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm7, ymm7, ymm14
	vpsraw ymm14, ymm7, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm7, ymm7, ymm14
	vpmullw ymm9, ymm6, ymm13
	vpmulhw ymm6, ymm6, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm6, ymm6, ymm9
	vpsraw ymm9, ymm6, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm6, ymm6, ymm9
	vpmullw ymm12, ymm0, ymm13
	vpmulhw ymm0, ymm0, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm0, ymm0, ymm12
	vpsraw ymm12, ymm0, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm0, ymm0, ymm12
	vpmullw ymm5, ymm1, ymm13
	vpmulhw ymm1, ymm1, ymm10
	vpmulhw ymm5, ymm5, ymm15
	vpsubw ymm1, ymm1, ymm5
	vpsraw ymm5, ymm1, 15
	vpand ymm5, ymm5, ymm15
	vpaddw ymm1, ymm1, ymm5
	vpmullw ymm3, ymm2, ymm13
	vpmulhw ymm2, ymm2, ymm10
	vpmulhw ymm3, ymm3, ymm15
	vpsubw ymm2, ymm2, ymm3
	vpsraw ymm3, ymm2, 15
	vpand ymm3, ymm3, ymm15
	vpaddw ymm2, ymm2, ymm3
	vpmullw ymm14, ymm11, ymm13
	vpmulhw ymm11, ymm11, ymm10
	vpmulhw ymm14, ymm14, ymm15
	vpsubw ymm11, ymm11, ymm14
	vpsraw ymm14, ymm11, 15
	vpand ymm14, ymm14, ymm15
	vpaddw ymm11, ymm11, ymm14
	vpmullw ymm9, ymm4, ymm13
	vpmulhw ymm4, ymm4, ymm10
	vpmulhw ymm9, ymm9, ymm15
	vpsubw ymm4, ymm4, ymm9
	vpsraw ymm9, ymm4, 15
	vpand ymm9, ymm9, ymm15
	vpaddw ymm4, ymm4, ymm9
	vpmullw ymm12, ymm8, ymm13
	vpmulhw ymm8, ymm8, ymm10
	vpmulhw ymm12, ymm12, ymm15
	vpsubw ymm8, ymm8, ymm12
	vpsraw ymm12, ymm8, 15
	vpand ymm12, ymm12, ymm15
	vpaddw ymm8, ymm8, ymm12
	vpunpckldq ymm5, ymm7, ymm6
	vpunpckhdq ymm6, ymm7, ymm6
	vpunpckldq ymm3, ymm0, ymm1
	vpunpckhdq ymm1, ymm0, ymm1
	vpunpckldq ymm14, ymm2, ymm11
	vpunpckhdq ymm11, ymm2, ymm11
	vpunpckldq ymm9, ymm4, ymm8
	vpunpckhdq ymm8, ymm4, ymm8
	vpxor ymm12, ymm12, ymm12
	vpermq ymm5, ymm5, 216
	vpunpckhwd ymm10, ymm5, ymm12
	vpunpcklwd ymm5, ymm5, ymm12
	vmovdqu YMMWORD PTR [r10+512], ymm5
	vmovdqu YMMWORD PTR [r10+576], ymm10
	vpermq ymm6, ymm6, 216
	vpunpckhwd ymm10, ymm6, ymm12
	vpunpcklwd ymm6, ymm6, ymm12
	vmovdqu YMMWORD PTR [r10+544], ymm6
	vmovdqu YMMWORD PTR [r10+608], ymm10
	vpermq ymm3, ymm3, 216
	vpunpckhwd ymm13, ymm3, ymm12
	vpunpcklwd ymm3, ymm3, ymm12
	vmovdqu YMMWORD PTR [r10+640], ymm3
	vmovdqu YMMWORD PTR [r10+704], ymm13
	vpermq ymm1, ymm1, 216
	vpunpckhwd ymm13, ymm1, ymm12
	vpunpcklwd ymm1, ymm1, ymm12
	vmovdqu YMMWORD PTR [r10+672], ymm1
	vmovdqu YMMWORD PTR [r10+736], ymm13
	vpermq ymm14, ymm14, 216
	vpunpckhwd ymm7, ymm14, ymm12
	vpunpcklwd ymm14, ymm14, ymm12
	vmovdqu YMMWORD PTR [r10+768], ymm14
	vmovdqu YMMWORD PTR [r10+832], ymm7
	vpermq ymm11, ymm11, 216
	vpunpckhwd ymm7, ymm11, ymm12
	vpunpcklwd ymm11, ymm11, ymm12
	vmovdqu YMMWORD PTR [r10+800], ymm11
	vmovdqu YMMWORD PTR [r10+864], ymm7
	vpermq ymm9, ymm9, 216
	vpunpckhwd ymm0, ymm9, ymm12
	vpunpcklwd ymm9, ymm9, ymm12
	vmovdqu YMMWORD PTR [r10+896], ymm9
	vmovdqu YMMWORD PTR [r10+960], ymm0
	vpermq ymm8, ymm8, 216
	vpunpckhwd ymm0, ymm8, ymm12
	vpunpcklwd ymm8, ymm8, ymm12
	vmovdqu YMMWORD PTR [r10+928], ymm8
	vmovdqu YMMWORD PTR [r10+992], ymm0
	vzeroupper
	add r12, 1024
	add r15, 512
	add rbp, 1024
	sub r14, 1
	jne 23b
	lfence
	mov DWORD PTR [rbx+768], r11d
	ldmxcsr DWORD PTR [rbx+768]
	sub r12, 3072
	mov rdi, r12
	add rdi, 0
	mov rsi, r13
	add rsi, 0
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1248]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+1280]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+1312]
	mov ecx, 8
24:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vpackssdw ymm0, ymm0, ymm1
	vpermq ymm0, ymm0, 216
	vpsrld ymm1, ymm0, 16
	vpslld ymm1, ymm1, 12
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpaddd ymm0, ymm0, ymm1
	vpshufb ymm0, ymm0, ymm8
	vmovdqu ymm2, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpackssdw ymm2, ymm2, ymm3
	vpermq ymm2, ymm2, 216
	vpsrld ymm3, ymm2, 16
	vpslld ymm3, ymm3, 12
	vpslld ymm2, ymm2, 16
	vpsrld ymm2, ymm2, 16
	vpaddd ymm2, ymm2, ymm3
	vpshufb ymm2, ymm2, ymm8
	vpermd ymm0, ymm9, ymm0
	vpermd ymm2, ymm10, ymm2
	vpblendd ymm0, ymm0, ymm2, 192
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu XMMWORD PTR [rsi+32], xmm2
	add rdi, 128
	add rsi, 48
	sub rcx, 1
	jne 24b
	vzeroupper
	mov rdi, r12
	add rdi, 1024
	mov rsi, r13
	add rsi, 384
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1248]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+1280]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+1312]
	mov ecx, 8
25:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vpackssdw ymm0, ymm0, ymm1
	vpermq ymm0, ymm0, 216
	vpsrld ymm1, ymm0, 16
	vpslld ymm1, ymm1, 12
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpaddd ymm0, ymm0, ymm1
	vpshufb ymm0, ymm0, ymm8
	vmovdqu ymm2, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpackssdw ymm2, ymm2, ymm3
	vpermq ymm2, ymm2, 216
	vpsrld ymm3, ymm2, 16
	vpslld ymm3, ymm3, 12
	vpslld ymm2, ymm2, 16
	vpsrld ymm2, ymm2, 16
	vpaddd ymm2, ymm2, ymm3
	vpshufb ymm2, ymm2, ymm8
	vpermd ymm0, ymm9, ymm0
	vpermd ymm2, ymm10, ymm2
	vpblendd ymm0, ymm0, ymm2, 192
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu XMMWORD PTR [rsi+32], xmm2
	add rdi, 128
	add rsi, 48
	sub rcx, 1
	jne 25b
	vzeroupper
	mov rdi, r12
	add rdi, 2048
	mov rsi, r13
	add rsi, 768
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm8, YMMWORD PTR [rax+1248]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm9, YMMWORD PTR [rax+1280]
	lea rax, {VG_MLKEM_YCONSTS}
	vmovdqu ymm10, YMMWORD PTR [rax+1312]
	mov ecx, 8
26:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vpackssdw ymm0, ymm0, ymm1
	vpermq ymm0, ymm0, 216
	vpsrld ymm1, ymm0, 16
	vpslld ymm1, ymm1, 12
	vpslld ymm0, ymm0, 16
	vpsrld ymm0, ymm0, 16
	vpaddd ymm0, ymm0, ymm1
	vpshufb ymm0, ymm0, ymm8
	vmovdqu ymm2, YMMWORD PTR [rdi+64]
	vmovdqu ymm3, YMMWORD PTR [rdi+96]
	vpackssdw ymm2, ymm2, ymm3
	vpermq ymm2, ymm2, 216
	vpsrld ymm3, ymm2, 16
	vpslld ymm3, ymm3, 12
	vpslld ymm2, ymm2, 16
	vpsrld ymm2, ymm2, 16
	vpaddd ymm2, ymm2, ymm3
	vpshufb ymm2, ymm2, ymm8
	vpermd ymm0, ymm9, ymm0
	vpermd ymm2, ymm10, ymm2
	vpblendd ymm0, ymm0, ymm2, 192
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu XMMWORD PTR [rsi+32], xmm2
	add rdi, 128
	add rsi, 48
	sub rcx, 1
	jne 26b
	vzeroupper
	mov rbp, QWORD PTR [rbx+3072]
	mov r12, QWORD PTR [rbx+3080]
	mov r13, QWORD PTR [rbx+3088]
	mov r14, QWORD PTR [rbx+3096]
	mov r15, QWORD PTR [rbx+3104]
	mov rbx, QWORD PTR [rbx+3112]
	ret
	.p2align 6
