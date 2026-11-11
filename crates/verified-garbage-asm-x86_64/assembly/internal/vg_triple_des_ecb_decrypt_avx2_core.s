// The functions of `src/internal/vg_triple_des_ecb_decrypt_avx2_core.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_ecb_decrypt_avx2_core:
	lea rsp, [rsp-1032]
	mov rcx, rsp
	add rcx, 8
	cmp rdx, 256
	jb 20f
	mov QWORD PTR [rcx+1016], rbx
	mov QWORD PTR [rcx+1008], r12
	mov QWORD PTR [rcx+1000], r13
22:
	mov r11, 8
23:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 23b
	sub rsi, 256
	mov r11, 8
24:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 24b
	sub rsi, 2048
	movabs rbx, -1
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	mov r11, 3
25:
	cmp r11, 3
	je 26f
	cmp r11, 2
	je 28f
	mov r8, rdi
	add r8, 120
	mov r9, -8
	jmp 29f
28:
	mov r8, rdi
	add r8, 128
	mov r9, 8
29:
	jmp 27f
26:
	mov r8, rdi
	add r8, 376
	mov r9, -8
27:
	mov r10, 16
	mov r12, rsi
	add r12, 32
	mov r13, rsi
210:
	mov rax, QWORD PTR [r8]
	add r8, r9
	ror rax, 48
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1984]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1728]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1472]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1216]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+960]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm1, ymm5
	vpxor ymm7, ymm2, ymm6
	vpor ymm8, ymm3, ymm0
	vpxor ymm9, ymm5, ymm3
	vpand ymm10, ymm8, ymm9
	vpxor ymm11, ymm2, ymm10
	vpandn ymm12, ymm7, ymm11
	vpxor ymm13, ymm1, ymm0
	vpxor ymm14, ymm3, ymm13
	vpandn ymm14, ymm14, ymm7
	vpor ymm10, ymm0, ymm10
	vpxor ymm10, ymm14, ymm10
	vpandn ymm14, ymm12, ymm10
	vpor ymm0, ymm5, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm14
	vpor ymm14, ymm10, ymm0
	vpandn ymm11, ymm11, ymm1
	vmovdqu YMMWORD PTR [rcx+32], ymm1
	vpxor ymm1, ymm14, ymm11
	vpandn ymm0, ymm0, ymm2
	vpxor ymm0, ymm11, ymm0
	vpandn ymm9, ymm9, ymm13
	vpor ymm9, ymm0, ymm9
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm7, ymm14
	vpandn ymm6, ymm6, ymm3
	vpxor ymm3, ymm6, ymm15
	vpand ymm10, ymm8, ymm10
	vpxor ymm10, ymm3, ymm10
	vpandn ymm1, ymm4, ymm1
	vpxor ymm1, ymm1, ymm10
	vpxor ymm6, ymm13, ymm6
	vpor ymm6, ymm11, ymm6
	vpxor ymm6, ymm8, ymm6
	vpxor ymm6, ymm5, ymm6
	vpxor ymm10, ymm10, ymm6
	vpor ymm12, ymm12, ymm4
	vpxor ymm12, ymm12, ymm10
	vpxor ymm14, ymm8, ymm14
	vpor ymm14, ymm9, ymm14
	vpxor ymm14, ymm6, ymm14
	vpor ymm10, ymm13, ymm10
	vpxor ymm10, ymm14, ymm10
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpor ymm8, ymm13, ymm4
	vpxor ymm10, ymm8, ymm10
	vmovdqu ymm8, YMMWORD PTR [rcx+32]
	vpor ymm7, ymm8, ymm7
	vpandn ymm14, ymm14, ymm7
	vpand ymm6, ymm13, ymm6
	vpxor ymm6, ymm14, ymm6
	vpor ymm4, ymm6, ymm4
	vpxor ymm9, ymm4, ymm9
	vmovdqa ymm0, ymm9
	vmovdqa ymm2, ymm10
	vmovdqa ymm3, ymm12
	vmovdqu ymm14, YMMWORD PTR [r13+256]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+256], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+320]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+320], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1856]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1856], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1920]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1920], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1216]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+960]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+704]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+448]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+192]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1920]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpandn ymm7, ymm0, ymm5
	vpandn ymm7, ymm7, ymm1
	vpor ymm8, ymm4, ymm7
	vpandn ymm9, ymm0, ymm6
	vpand ymm10, ymm5, ymm6
	vpxor ymm10, ymm1, ymm10
	vpandn ymm1, ymm9, ymm10
	vpand ymm11, ymm3, ymm0
	vpxor ymm9, ymm7, ymm9
	vpand ymm9, ymm8, ymm9
	vpandn ymm7, ymm11, ymm9
	vpand ymm12, ymm3, ymm9
	vpxor ymm5, ymm5, ymm15
	vpxor ymm5, ymm12, ymm5
	vpxor ymm0, ymm0, ymm6
	vpandn ymm13, ymm11, ymm0
	vpxor ymm14, ymm5, ymm13
	vpandn ymm7, ymm7, ymm2
	vpxor ymm7, ymm7, ymm14
	vpandn ymm13, ymm13, ymm4
	vpxor ymm10, ymm10, ymm13
	vpandn ymm5, ymm10, ymm5
	vpxor ymm3, ymm3, ymm0
	vpxor ymm5, ymm5, ymm3
	vpandn ymm4, ymm2, ymm8
	vpxor ymm4, ymm4, ymm5
	vpxor ymm13, ymm12, ymm13
	vpor ymm13, ymm3, ymm13
	vpxor ymm8, ymm8, ymm14
	vpor ymm11, ymm11, ymm8
	vpxor ymm3, ymm13, ymm11
	vpxor ymm14, ymm9, ymm14
	vpxor ymm14, ymm5, ymm14
	vpand ymm14, ymm11, ymm14
	vpand ymm13, ymm6, ymm13
	vpxor ymm13, ymm14, ymm13
	vpor ymm14, ymm13, ymm2
	vpxor ymm3, ymm14, ymm3
	vpandn ymm10, ymm10, ymm13
	vpor ymm8, ymm0, ymm8
	vpxor ymm8, ymm10, ymm8
	vpor ymm2, ymm1, ymm2
	vpxor ymm8, ymm2, ymm8
	vmovdqa ymm0, ymm8
	vmovdqa ymm1, ymm3
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm4
	vmovdqu ymm14, YMMWORD PTR [r13+1600]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1600], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1728]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1728], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1024]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1024], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+896]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+896], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+192]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1920]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1664]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1408]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1152]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+896]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm5
	vpxor ymm7, ymm3, ymm0
	vpor ymm8, ymm6, ymm7
	vpxor ymm9, ymm2, ymm0
	vpandn ymm10, ymm5, ymm9
	vpxor ymm11, ymm8, ymm10
	vpxor ymm12, ymm4, ymm7
	vpandn ymm13, ymm0, ymm12
	vpxor ymm13, ymm8, ymm13
	vpandn ymm8, ymm13, ymm11
	vpand ymm14, ymm0, ymm11
	vpor ymm14, ymm2, ymm14
	vpand ymm14, ymm5, ymm14
	vpxor ymm14, ymm12, ymm14
	vmovdqu YMMWORD PTR [rcx], ymm6
	vpandn ymm6, ymm1, ymm11
	vpxor ymm6, ymm6, ymm14
	vpand ymm9, ymm7, ymm9
	vpxor ymm7, ymm5, ymm2
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm13, ymm7
	vpor ymm6, ymm3, ymm6
	vpandn ymm9, ymm9, ymm6
	vpor ymm7, ymm10, ymm7
	vpandn ymm10, ymm7, ymm14
	vpand ymm0, ymm2, ymm0
	vpandn ymm6, ymm4, ymm0
	vpxor ymm6, ymm10, ymm6
	vpand ymm13, ymm13, ymm6
	vpor ymm0, ymm12, ymm0
	vpandn ymm13, ymm13, ymm0
	vpxor ymm13, ymm5, ymm13
	vpand ymm9, ymm9, ymm1
	vpxor ymm9, ymm9, ymm13
	vpxor ymm11, ymm11, ymm15
	vpor ymm4, ymm4, ymm11
	vpor ymm4, ymm3, ymm4
	vpxor ymm4, ymm12, ymm4
	vpxor ymm7, ymm7, ymm4
	vpandn ymm8, ymm8, ymm1
	vpxor ymm7, ymm8, ymm7
	vpand ymm11, ymm2, ymm11
	vpxor ymm11, ymm14, ymm11
	vpor ymm11, ymm4, ymm11
	vmovdqu ymm4, YMMWORD PTR [rcx]
	vpxor ymm13, ymm4, ymm13
	vpxor ymm13, ymm11, ymm13
	vpor ymm1, ymm6, ymm1
	vpxor ymm13, ymm1, ymm13
	vmovdqu ymm0, YMMWORD PTR [rcx+32]
	vmovdqa ymm1, ymm13
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm7
	vmovdqu ymm14, YMMWORD PTR [r13+704]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+704], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+512]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+512], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+128]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+128], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+64]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+64], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1152]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+896]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+640]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+384]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+128]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1856]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm5, ymm5, ymm3
	vpxor ymm3, ymm3, ymm1
	vpor ymm6, ymm4, ymm2
	vpxor ymm6, ymm1, ymm6
	vpandn ymm6, ymm6, ymm3
	vpandn ymm7, ymm4, ymm3
	vpxor ymm8, ymm2, ymm7
	vpor ymm9, ymm5, ymm8
	vpandn ymm9, ymm6, ymm9
	vpxor ymm10, ymm4, ymm9
	vpand ymm8, ymm8, ymm10
	vpandn ymm3, ymm8, ymm3
	vpxor ymm5, ymm5, ymm10
	vpandn ymm3, ymm3, ymm5
	vpxor ymm3, ymm6, ymm3
	vpxor ymm2, ymm4, ymm2
	vpor ymm7, ymm1, ymm7
	vpxor ymm7, ymm5, ymm7
	vpandn ymm5, ymm2, ymm7
	vpxor ymm5, ymm9, ymm5
	vpandn ymm9, ymm3, ymm0
	vpxor ymm9, ymm9, ymm5
	vpxor ymm5, ymm5, ymm15
	vpandn ymm1, ymm0, ymm3
	vpxor ymm1, ymm1, ymm5
	vpxor ymm5, ymm3, ymm5
	vpandn ymm2, ymm2, ymm5
	vpor ymm2, ymm8, ymm2
	vpxor ymm2, ymm7, ymm2
	vpor ymm7, ymm10, ymm0
	vpxor ymm7, ymm7, ymm2
	vpand ymm10, ymm0, ymm10
	vpxor ymm2, ymm10, ymm2
	vmovdqa ymm0, ymm2
	vmovdqu YMMWORD PTR [rcx], ymm1
	vmovdqa ymm1, ymm7
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm9
	vmovdqu ymm14, YMMWORD PTR [r13+1984]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1984], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1664]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1664], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1088]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1088], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1536]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1536], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+128]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1856]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1600]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1344]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1088]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+832]
	vpxor ymm0, ymm0, ymm14
	vpor ymm6, ymm5, ymm3
	vpandn ymm7, ymm0, ymm6
	vpxor ymm8, ymm5, ymm7
	vpxor ymm9, ymm3, ymm8
	vpor ymm10, ymm2, ymm9
	vpandn ymm7, ymm2, ymm7
	vpxor ymm7, ymm3, ymm7
	vpand ymm3, ymm1, ymm7
	vpor ymm9, ymm5, ymm9
	vpxor ymm3, ymm3, ymm9
	vpxor ymm3, ymm2, ymm3
	vpxor ymm0, ymm0, ymm3
	vpor ymm11, ymm8, ymm0
	vpand ymm12, ymm1, ymm11
	vpxor ymm13, ymm8, ymm12
	vpand ymm14, ymm2, ymm9
	vpxor ymm14, ymm13, ymm14
	vpandn ymm11, ymm5, ymm11
	vpxor ymm13, ymm7, ymm11
	vpxor ymm1, ymm1, ymm10
	vpandn ymm13, ymm13, ymm1
	vpxor ymm13, ymm13, ymm15
	vpandn ymm13, ymm4, ymm13
	vpxor ymm3, ymm13, ymm3
	vpandn ymm13, ymm12, ymm7
	vpxor ymm11, ymm11, ymm1
	vpor ymm11, ymm14, ymm11
	vpandn ymm13, ymm13, ymm11
	vpandn ymm11, ymm13, ymm10
	vpand ymm0, ymm0, ymm13
	vpxor ymm0, ymm1, ymm0
	vpand ymm9, ymm7, ymm9
	vpor ymm9, ymm0, ymm9
	vpxor ymm9, ymm12, ymm9
	vpand ymm9, ymm9, ymm4
	vpxor ymm14, ymm9, ymm14
	vpxor ymm6, ymm5, ymm6
	vpxor ymm6, ymm13, ymm6
	vpand ymm2, ymm2, ymm0
	vpxor ymm2, ymm6, ymm2
	vpor ymm11, ymm11, ymm4
	vpxor ymm11, ymm11, ymm2
	vpxor ymm7, ymm10, ymm7
	vpandn ymm2, ymm2, ymm7
	vpxor ymm0, ymm8, ymm0
	vpxor ymm0, ymm2, ymm0
	vpand ymm4, ymm10, ymm4
	vpxor ymm0, ymm4, ymm0
	vmovdqu YMMWORD PTR [rcx], ymm0
	vmovdqa ymm0, ymm14
	vmovdqa ymm1, ymm3
	vmovdqu ymm2, YMMWORD PTR [rcx]
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1472]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1472], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1792]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1792], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+640]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+640], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+192]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+192], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1088]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+832]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+576]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+320]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+64]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1792]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm4, ymm1
	vpor ymm7, ymm4, ymm0
	vpand ymm7, ymm5, ymm7
	vpxor ymm6, ymm6, ymm7
	vpxor ymm8, ymm0, ymm6
	vpandn ymm9, ymm8, ymm1
	vpand ymm8, ymm5, ymm8
	vpxor ymm10, ymm4, ymm8
	vpxor ymm11, ymm5, ymm3
	vpor ymm12, ymm10, ymm11
	vpxor ymm13, ymm6, ymm12
	vpand ymm14, ymm3, ymm13
	vmovdqu YMMWORD PTR [rcx], ymm8
	vpandn ymm8, ymm0, ymm14
	vpor ymm10, ymm9, ymm10
	vmovdqu YMMWORD PTR [rcx+32], ymm6
	vpxor ymm6, ymm8, ymm10
	vmovdqu YMMWORD PTR [rcx+64], ymm9
	vpand ymm9, ymm6, ymm2
	vpxor ymm9, ymm9, ymm13
	vpxor ymm12, ymm4, ymm12
	vmovdqu YMMWORD PTR [rcx+96], ymm9
	vpandn ymm9, ymm12, ymm0
	vpxor ymm9, ymm3, ymm9
	vpandn ymm3, ymm14, ymm1
	vpor ymm3, ymm9, ymm3
	vpor ymm11, ymm4, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm7, ymm3
	vpxor ymm7, ymm6, ymm7
	vpor ymm13, ymm5, ymm13
	vpand ymm13, ymm10, ymm13
	vpxor ymm13, ymm9, ymm13
	vpandn ymm8, ymm8, ymm13
	vmovdqu ymm10, YMMWORD PTR [rcx+64]
	vpor ymm10, ymm10, ymm2
	vpxor ymm8, ymm10, ymm8
	vmovdqu ymm10, YMMWORD PTR [rcx+32]
	vpxor ymm13, ymm10, ymm13
	vpandn ymm13, ymm13, ymm1
	vpxor ymm11, ymm11, ymm15
	vpxor ymm11, ymm12, ymm11
	vpxor ymm13, ymm13, ymm11
	vpandn ymm13, ymm2, ymm13
	vpxor ymm7, ymm13, ymm7
	vmovdqu ymm13, YMMWORD PTR [rcx]
	vpxor ymm13, ymm0, ymm13
	vpxor ymm9, ymm5, ymm9
	vpand ymm9, ymm13, ymm9
	vpxor ymm11, ymm14, ymm11
	vpxor ymm11, ymm9, ymm11
	vpandn ymm2, ymm2, ymm3
	vpxor ymm11, ymm2, ymm11
	vmovdqu ymm0, YMMWORD PTR [rcx+96]
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+1344]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+1344], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+1408]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+1408], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+768]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+768], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+1216]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+1216], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+64]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+1792]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+1536]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+1280]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12+1024]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+768]
	vpxor ymm0, ymm0, ymm14
	vpxor ymm6, ymm2, ymm1
	vpxor ymm7, ymm3, ymm6
	vpand ymm8, ymm0, ymm7
	vpand ymm9, ymm2, ymm6
	vpxor ymm10, ymm4, ymm9
	vpand ymm11, ymm8, ymm10
	vpand ymm12, ymm0, ymm9
	vpxor ymm13, ymm3, ymm12
	vpor ymm14, ymm10, ymm13
	vpxor ymm6, ymm0, ymm6
	vmovdqu YMMWORD PTR [rcx], ymm0
	vpxor ymm0, ymm14, ymm6
	vmovdqu YMMWORD PTR [rcx+32], ymm9
	vpandn ymm9, ymm11, ymm5
	vpxor ymm0, ymm9, ymm0
	vpandn ymm7, ymm7, ymm1
	vpor ymm9, ymm10, ymm7
	vpxor ymm13, ymm8, ymm13
	vpxor ymm9, ymm9, ymm13
	vpxor ymm6, ymm8, ymm6
	vpandn ymm2, ymm6, ymm2
	vpandn ymm8, ymm2, ymm10
	vpxor ymm13, ymm1, ymm13
	vpxor ymm13, ymm8, ymm13
	vpandn ymm12, ymm12, ymm6
	vpor ymm2, ymm2, ymm12
	vpxor ymm14, ymm4, ymm14
	vpand ymm14, ymm13, ymm14
	vpxor ymm14, ymm2, ymm14
	vpand ymm6, ymm14, ymm5
	vpxor ymm6, ymm6, ymm13
	vpandn ymm3, ymm3, ymm10
	vpor ymm3, ymm12, ymm3
	vmovdqu ymm12, YMMWORD PTR [rcx+32]
	vpor ymm13, ymm12, ymm13
	vpand ymm13, ymm3, ymm13
	vpxor ymm14, ymm14, ymm13
	vpxor ymm2, ymm7, ymm2
	vmovdqu ymm7, YMMWORD PTR [rcx]
	vpand ymm2, ymm7, ymm2
	vpor ymm2, ymm11, ymm2
	vpxor ymm13, ymm13, ymm2
	vpandn ymm11, ymm5, ymm13
	vpxor ymm11, ymm11, ymm9
	vpand ymm2, ymm4, ymm2
	vpxor ymm9, ymm9, ymm15
	vpxor ymm9, ymm2, ymm9
	vpxor ymm9, ymm13, ymm9
	vpor ymm5, ymm14, ymm5
	vpxor ymm9, ymm5, ymm9
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm9
	vmovdqa ymm3, ymm11
	vmovdqu ymm14, YMMWORD PTR [r13+448]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+448], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+576]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+576], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1152]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1152], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13], ymm3
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm5, YMMWORD PTR [r12+1024]
	vpxor ymm5, ymm5, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm4, YMMWORD PTR [r12+768]
	vpxor ymm4, ymm4, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm3, YMMWORD PTR [r12+512]
	vpxor ymm3, ymm3, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm2, YMMWORD PTR [r12+256]
	vpxor ymm2, ymm2, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm1, YMMWORD PTR [r12]
	vpxor ymm1, ymm1, ymm14
	add rax, rax
	sbb rbx, rbx
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	vmovdqu ymm0, YMMWORD PTR [r12+1984]
	vpxor ymm0, ymm0, ymm14
	vpandn ymm6, ymm4, ymm3
	vpandn ymm7, ymm3, ymm1
	vpxor ymm7, ymm2, ymm7
	vpand ymm8, ymm5, ymm7
	vpandn ymm9, ymm6, ymm8
	vpandn ymm10, ymm7, ymm4
	vpor ymm11, ymm5, ymm10
	vpandn ymm12, ymm3, ymm4
	vpxor ymm12, ymm1, ymm12
	vpand ymm13, ymm11, ymm12
	vpor ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm15
	vpxor ymm7, ymm13, ymm7
	vpandn ymm11, ymm11, ymm3
	vpxor ymm11, ymm7, ymm11
	vpxor ymm6, ymm6, ymm11
	vpor ymm7, ymm9, ymm0
	vpxor ymm7, ymm7, ymm6
	vpxor ymm6, ymm5, ymm6
	vpand ymm3, ymm1, ymm6
	vpxor ymm11, ymm4, ymm11
	vpxor ymm3, ymm3, ymm11
	vpxor ymm10, ymm10, ymm3
	vpxor ymm3, ymm8, ymm3
	vpor ymm3, ymm4, ymm3
	vpxor ymm6, ymm1, ymm6
	vpxor ymm6, ymm3, ymm6
	vpand ymm8, ymm8, ymm0
	vpxor ymm8, ymm8, ymm6
	vpxor ymm12, ymm12, ymm10
	vpor ymm11, ymm2, ymm11
	vpxor ymm11, ymm12, ymm11
	vpxor ymm5, ymm5, ymm11
	vpand ymm5, ymm5, ymm0
	vpxor ymm5, ymm5, ymm10
	vpandn ymm2, ymm2, ymm12
	vpand ymm2, ymm6, ymm2
	vpxor ymm11, ymm9, ymm11
	vpxor ymm11, ymm2, ymm11
	vpor ymm0, ymm11, ymm0
	vpxor ymm10, ymm0, ymm10
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm8
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm10
	vmovdqu ymm14, YMMWORD PTR [r13+832]
	vpxor ymm0, ymm0, ymm14
	vmovdqu YMMWORD PTR [r13+832], ymm0
	vmovdqu ymm14, YMMWORD PTR [r13+384]
	vpxor ymm1, ymm1, ymm14
	vmovdqu YMMWORD PTR [r13+384], ymm1
	vmovdqu ymm14, YMMWORD PTR [r13+1280]
	vpxor ymm2, ymm2, ymm14
	vmovdqu YMMWORD PTR [r13+1280], ymm2
	vmovdqu ymm14, YMMWORD PTR [r13+960]
	vpxor ymm3, ymm3, ymm14
	vmovdqu YMMWORD PTR [r13+960], ymm3
	mov rbx, r12
	mov r12, r13
	mov r13, rbx
	sub r10, 1
	jne 210b
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu YMMWORD PTR [rsi], ymm1
	vmovdqu YMMWORD PTR [rsi+32], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+256]
	vmovdqu ymm1, YMMWORD PTR [rsi+288]
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+288], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+512]
	vmovdqu ymm1, YMMWORD PTR [rsi+544]
	vmovdqu YMMWORD PTR [rsi+512], ymm1
	vmovdqu YMMWORD PTR [rsi+544], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+768]
	vmovdqu ymm1, YMMWORD PTR [rsi+800]
	vmovdqu YMMWORD PTR [rsi+768], ymm1
	vmovdqu YMMWORD PTR [rsi+800], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1024]
	vmovdqu ymm1, YMMWORD PTR [rsi+1056]
	vmovdqu YMMWORD PTR [rsi+1024], ymm1
	vmovdqu YMMWORD PTR [rsi+1056], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1280]
	vmovdqu ymm1, YMMWORD PTR [rsi+1312]
	vmovdqu YMMWORD PTR [rsi+1280], ymm1
	vmovdqu YMMWORD PTR [rsi+1312], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1536]
	vmovdqu ymm1, YMMWORD PTR [rsi+1568]
	vmovdqu YMMWORD PTR [rsi+1536], ymm1
	vmovdqu YMMWORD PTR [rsi+1568], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1792]
	vmovdqu ymm1, YMMWORD PTR [rsi+1824]
	vmovdqu YMMWORD PTR [rsi+1792], ymm1
	vmovdqu YMMWORD PTR [rsi+1824], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+64]
	vmovdqu ymm1, YMMWORD PTR [rsi+96]
	vmovdqu YMMWORD PTR [rsi+64], ymm1
	vmovdqu YMMWORD PTR [rsi+96], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+320]
	vmovdqu ymm1, YMMWORD PTR [rsi+352]
	vmovdqu YMMWORD PTR [rsi+320], ymm1
	vmovdqu YMMWORD PTR [rsi+352], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+576]
	vmovdqu ymm1, YMMWORD PTR [rsi+608]
	vmovdqu YMMWORD PTR [rsi+576], ymm1
	vmovdqu YMMWORD PTR [rsi+608], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+832]
	vmovdqu ymm1, YMMWORD PTR [rsi+864]
	vmovdqu YMMWORD PTR [rsi+832], ymm1
	vmovdqu YMMWORD PTR [rsi+864], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1088]
	vmovdqu ymm1, YMMWORD PTR [rsi+1120]
	vmovdqu YMMWORD PTR [rsi+1088], ymm1
	vmovdqu YMMWORD PTR [rsi+1120], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1344]
	vmovdqu ymm1, YMMWORD PTR [rsi+1376]
	vmovdqu YMMWORD PTR [rsi+1344], ymm1
	vmovdqu YMMWORD PTR [rsi+1376], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1600]
	vmovdqu ymm1, YMMWORD PTR [rsi+1632]
	vmovdqu YMMWORD PTR [rsi+1600], ymm1
	vmovdqu YMMWORD PTR [rsi+1632], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1856]
	vmovdqu ymm1, YMMWORD PTR [rsi+1888]
	vmovdqu YMMWORD PTR [rsi+1856], ymm1
	vmovdqu YMMWORD PTR [rsi+1888], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+128]
	vmovdqu ymm1, YMMWORD PTR [rsi+160]
	vmovdqu YMMWORD PTR [rsi+128], ymm1
	vmovdqu YMMWORD PTR [rsi+160], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+384]
	vmovdqu ymm1, YMMWORD PTR [rsi+416]
	vmovdqu YMMWORD PTR [rsi+384], ymm1
	vmovdqu YMMWORD PTR [rsi+416], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+640]
	vmovdqu ymm1, YMMWORD PTR [rsi+672]
	vmovdqu YMMWORD PTR [rsi+640], ymm1
	vmovdqu YMMWORD PTR [rsi+672], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+896]
	vmovdqu ymm1, YMMWORD PTR [rsi+928]
	vmovdqu YMMWORD PTR [rsi+896], ymm1
	vmovdqu YMMWORD PTR [rsi+928], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1152]
	vmovdqu ymm1, YMMWORD PTR [rsi+1184]
	vmovdqu YMMWORD PTR [rsi+1152], ymm1
	vmovdqu YMMWORD PTR [rsi+1184], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1408]
	vmovdqu ymm1, YMMWORD PTR [rsi+1440]
	vmovdqu YMMWORD PTR [rsi+1408], ymm1
	vmovdqu YMMWORD PTR [rsi+1440], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1664]
	vmovdqu ymm1, YMMWORD PTR [rsi+1696]
	vmovdqu YMMWORD PTR [rsi+1664], ymm1
	vmovdqu YMMWORD PTR [rsi+1696], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1920]
	vmovdqu ymm1, YMMWORD PTR [rsi+1952]
	vmovdqu YMMWORD PTR [rsi+1920], ymm1
	vmovdqu YMMWORD PTR [rsi+1952], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+192]
	vmovdqu ymm1, YMMWORD PTR [rsi+224]
	vmovdqu YMMWORD PTR [rsi+192], ymm1
	vmovdqu YMMWORD PTR [rsi+224], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+448]
	vmovdqu ymm1, YMMWORD PTR [rsi+480]
	vmovdqu YMMWORD PTR [rsi+448], ymm1
	vmovdqu YMMWORD PTR [rsi+480], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+704]
	vmovdqu ymm1, YMMWORD PTR [rsi+736]
	vmovdqu YMMWORD PTR [rsi+704], ymm1
	vmovdqu YMMWORD PTR [rsi+736], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+960]
	vmovdqu ymm1, YMMWORD PTR [rsi+992]
	vmovdqu YMMWORD PTR [rsi+960], ymm1
	vmovdqu YMMWORD PTR [rsi+992], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1216]
	vmovdqu ymm1, YMMWORD PTR [rsi+1248]
	vmovdqu YMMWORD PTR [rsi+1216], ymm1
	vmovdqu YMMWORD PTR [rsi+1248], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1472]
	vmovdqu ymm1, YMMWORD PTR [rsi+1504]
	vmovdqu YMMWORD PTR [rsi+1472], ymm1
	vmovdqu YMMWORD PTR [rsi+1504], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1728]
	vmovdqu ymm1, YMMWORD PTR [rsi+1760]
	vmovdqu YMMWORD PTR [rsi+1728], ymm1
	vmovdqu YMMWORD PTR [rsi+1760], ymm0
	vmovdqu ymm0, YMMWORD PTR [rsi+1984]
	vmovdqu ymm1, YMMWORD PTR [rsi+2016]
	vmovdqu YMMWORD PTR [rsi+1984], ymm1
	vmovdqu YMMWORD PTR [rsi+2016], ymm0
	sub r11, 1
	jne 25b
	mov r11, 8
211:
	movabs rbx, 4294967295
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 281470681808895
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 71777214294589695
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+256]
	vmovdqu ymm2, YMMWORD PTR [rsi+512]
	vmovdqu ymm3, YMMWORD PTR [rsi+768]
	vmovdqu ymm4, YMMWORD PTR [rsi+1024]
	vmovdqu ymm5, YMMWORD PTR [rsi+1280]
	vmovdqu ymm6, YMMWORD PTR [rsi+1536]
	vmovdqu ymm7, YMMWORD PTR [rsi+1792]
	vpsrlq ymm8, ymm0, 32
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 32
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 32
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 32
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 32
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 16
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 16
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 16
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 16
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 16
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 8
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 8
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 8
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 8
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 8
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+256], ymm1
	vmovdqu YMMWORD PTR [rsi+512], ymm2
	vmovdqu YMMWORD PTR [rsi+768], ymm3
	vmovdqu YMMWORD PTR [rsi+1024], ymm4
	vmovdqu YMMWORD PTR [rsi+1280], ymm5
	vmovdqu YMMWORD PTR [rsi+1536], ymm6
	vmovdqu YMMWORD PTR [rsi+1792], ymm7
	add rsi, 32
	sub r11, 1
	jne 211b
	sub rsi, 256
	mov r11, 8
212:
	movabs rbx, 1085102592571150095
	vmovq xmm13, rbx
	vpbroadcastq ymm13, xmm13
	movabs rbx, 3689348814741910323
	vmovq xmm14, rbx
	vpbroadcastq ymm14, xmm14
	movabs rbx, 6148914691236517205
	vmovq xmm15, rbx
	vpbroadcastq ymm15, xmm15
	vmovdqu ymm0, YMMWORD PTR [rsi]
	vmovdqu ymm1, YMMWORD PTR [rsi+32]
	vmovdqu ymm2, YMMWORD PTR [rsi+64]
	vmovdqu ymm3, YMMWORD PTR [rsi+96]
	vmovdqu ymm4, YMMWORD PTR [rsi+128]
	vmovdqu ymm5, YMMWORD PTR [rsi+160]
	vmovdqu ymm6, YMMWORD PTR [rsi+192]
	vmovdqu ymm7, YMMWORD PTR [rsi+224]
	vpsrlq ymm8, ymm0, 4
	vpxor ymm8, ymm8, ymm4
	vpand ymm8, ymm8, ymm13
	vpxor ymm4, ymm4, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 4
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm13
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm2, 4
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm13
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm3, 4
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm13
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 4
	vpxor ymm3, ymm3, ymm8
	vpsrlq ymm8, ymm0, 2
	vpxor ymm8, ymm8, ymm2
	vpand ymm8, ymm8, ymm14
	vpxor ymm2, ymm2, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm1, 2
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm14
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm1, ymm1, ymm8
	vpsrlq ymm8, ymm4, 2
	vpxor ymm8, ymm8, ymm6
	vpand ymm8, ymm8, ymm14
	vpxor ymm6, ymm6, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm5, 2
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm14
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 2
	vpxor ymm5, ymm5, ymm8
	vpsrlq ymm8, ymm0, 1
	vpxor ymm8, ymm8, ymm1
	vpand ymm8, ymm8, ymm15
	vpxor ymm1, ymm1, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm0, ymm0, ymm8
	vpsrlq ymm8, ymm2, 1
	vpxor ymm8, ymm8, ymm3
	vpand ymm8, ymm8, ymm15
	vpxor ymm3, ymm3, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm2, ymm2, ymm8
	vpsrlq ymm8, ymm4, 1
	vpxor ymm8, ymm8, ymm5
	vpand ymm8, ymm8, ymm15
	vpxor ymm5, ymm5, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm4, ymm4, ymm8
	vpsrlq ymm8, ymm6, 1
	vpxor ymm8, ymm8, ymm7
	vpand ymm8, ymm8, ymm15
	vpxor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm8, 1
	vpxor ymm6, ymm6, ymm8
	vmovdqu YMMWORD PTR [rsi], ymm0
	vmovdqu YMMWORD PTR [rsi+32], ymm1
	vmovdqu YMMWORD PTR [rsi+64], ymm2
	vmovdqu YMMWORD PTR [rsi+96], ymm3
	vmovdqu YMMWORD PTR [rsi+128], ymm4
	vmovdqu YMMWORD PTR [rsi+160], ymm5
	vmovdqu YMMWORD PTR [rsi+192], ymm6
	vmovdqu YMMWORD PTR [rsi+224], ymm7
	add rsi, 256
	sub r11, 1
	jne 212b
	sub rsi, 2048
	add rsi, 2048
	sub rdx, 256
	cmp rdx, 256
	jae 22b
	mov rbx, QWORD PTR [rcx+1016]
	mov r12, QWORD PTR [rcx+1008]
	mov r13, QWORD PTR [rcx+1000]
	vzeroupper
	jmp 21f
20:
21:
	call {vg_triple_des_ecb_decrypt_scratch}
	mov r11d, 0
	mov QWORD PTR [rsp+8], r11
	mov QWORD PTR [rsp+16], r11
	mov QWORD PTR [rsp+24], r11
	mov QWORD PTR [rsp+32], r11
	mov QWORD PTR [rsp+40], r11
	mov QWORD PTR [rsp+48], r11
	mov QWORD PTR [rsp+56], r11
	mov QWORD PTR [rsp+64], r11
	mov QWORD PTR [rsp+72], r11
	mov QWORD PTR [rsp+80], r11
	mov QWORD PTR [rsp+88], r11
	mov QWORD PTR [rsp+96], r11
	mov QWORD PTR [rsp+104], r11
	mov QWORD PTR [rsp+112], r11
	mov QWORD PTR [rsp+120], r11
	mov QWORD PTR [rsp+128], r11
	mov QWORD PTR [rsp+136], r11
	mov QWORD PTR [rsp+144], r11
	mov QWORD PTR [rsp+152], r11
	mov QWORD PTR [rsp+160], r11
	mov QWORD PTR [rsp+168], r11
	mov QWORD PTR [rsp+176], r11
	mov QWORD PTR [rsp+184], r11
	mov QWORD PTR [rsp+192], r11
	mov QWORD PTR [rsp+200], r11
	mov QWORD PTR [rsp+208], r11
	mov QWORD PTR [rsp+216], r11
	mov QWORD PTR [rsp+224], r11
	mov QWORD PTR [rsp+232], r11
	mov QWORD PTR [rsp+240], r11
	mov QWORD PTR [rsp+248], r11
	mov QWORD PTR [rsp+256], r11
	mov QWORD PTR [rsp+264], r11
	mov QWORD PTR [rsp+272], r11
	mov QWORD PTR [rsp+280], r11
	mov QWORD PTR [rsp+288], r11
	mov QWORD PTR [rsp+296], r11
	mov QWORD PTR [rsp+304], r11
	mov QWORD PTR [rsp+312], r11
	mov QWORD PTR [rsp+320], r11
	mov QWORD PTR [rsp+328], r11
	mov QWORD PTR [rsp+336], r11
	mov QWORD PTR [rsp+344], r11
	mov QWORD PTR [rsp+352], r11
	mov QWORD PTR [rsp+360], r11
	mov QWORD PTR [rsp+368], r11
	mov QWORD PTR [rsp+376], r11
	mov QWORD PTR [rsp+384], r11
	mov QWORD PTR [rsp+392], r11
	mov QWORD PTR [rsp+400], r11
	mov QWORD PTR [rsp+408], r11
	mov QWORD PTR [rsp+416], r11
	mov QWORD PTR [rsp+424], r11
	mov QWORD PTR [rsp+432], r11
	mov QWORD PTR [rsp+440], r11
	mov QWORD PTR [rsp+448], r11
	mov QWORD PTR [rsp+456], r11
	mov QWORD PTR [rsp+464], r11
	mov QWORD PTR [rsp+472], r11
	mov QWORD PTR [rsp+480], r11
	mov QWORD PTR [rsp+488], r11
	mov QWORD PTR [rsp+496], r11
	mov QWORD PTR [rsp+504], r11
	mov QWORD PTR [rsp+512], r11
	mov QWORD PTR [rsp+520], r11
	mov QWORD PTR [rsp+528], r11
	mov QWORD PTR [rsp+536], r11
	mov QWORD PTR [rsp+544], r11
	mov QWORD PTR [rsp+552], r11
	mov QWORD PTR [rsp+560], r11
	mov QWORD PTR [rsp+568], r11
	mov QWORD PTR [rsp+576], r11
	mov QWORD PTR [rsp+584], r11
	mov QWORD PTR [rsp+592], r11
	mov QWORD PTR [rsp+600], r11
	mov QWORD PTR [rsp+608], r11
	mov QWORD PTR [rsp+616], r11
	mov QWORD PTR [rsp+624], r11
	mov QWORD PTR [rsp+632], r11
	mov QWORD PTR [rsp+640], r11
	mov QWORD PTR [rsp+648], r11
	mov QWORD PTR [rsp+656], r11
	mov QWORD PTR [rsp+664], r11
	mov QWORD PTR [rsp+672], r11
	mov QWORD PTR [rsp+680], r11
	mov QWORD PTR [rsp+688], r11
	mov QWORD PTR [rsp+696], r11
	mov QWORD PTR [rsp+704], r11
	mov QWORD PTR [rsp+712], r11
	mov QWORD PTR [rsp+720], r11
	mov QWORD PTR [rsp+728], r11
	mov QWORD PTR [rsp+736], r11
	mov QWORD PTR [rsp+744], r11
	mov QWORD PTR [rsp+752], r11
	mov QWORD PTR [rsp+760], r11
	mov QWORD PTR [rsp+768], r11
	mov QWORD PTR [rsp+776], r11
	mov QWORD PTR [rsp+784], r11
	mov QWORD PTR [rsp+792], r11
	mov QWORD PTR [rsp+800], r11
	mov QWORD PTR [rsp+808], r11
	mov QWORD PTR [rsp+816], r11
	mov QWORD PTR [rsp+824], r11
	mov QWORD PTR [rsp+832], r11
	mov QWORD PTR [rsp+840], r11
	mov QWORD PTR [rsp+848], r11
	mov QWORD PTR [rsp+856], r11
	mov QWORD PTR [rsp+864], r11
	mov QWORD PTR [rsp+872], r11
	mov QWORD PTR [rsp+880], r11
	mov QWORD PTR [rsp+888], r11
	mov QWORD PTR [rsp+896], r11
	mov QWORD PTR [rsp+904], r11
	mov QWORD PTR [rsp+912], r11
	mov QWORD PTR [rsp+920], r11
	mov QWORD PTR [rsp+928], r11
	mov QWORD PTR [rsp+936], r11
	mov QWORD PTR [rsp+944], r11
	mov QWORD PTR [rsp+952], r11
	mov QWORD PTR [rsp+960], r11
	mov QWORD PTR [rsp+968], r11
	mov QWORD PTR [rsp+976], r11
	mov QWORD PTR [rsp+984], r11
	mov QWORD PTR [rsp+992], r11
	mov QWORD PTR [rsp+1000], r11
	mov QWORD PTR [rsp+1008], r11
	mov QWORD PTR [rsp+1016], r11
	mov QWORD PTR [rsp+1024], r11
	lea rsp, [rsp+1032]
	ret
	.p2align 6
