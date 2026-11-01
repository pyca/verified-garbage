// The functions of `src/internal/vg_poly1305_blocks_avx2.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_blocks_avx2:
	cmp rdx, 32
	jb 20f
	mov r8d, 67108863
	mov r9d, 16777216
	stmxcsr DWORD PTR [rdi+120]
	mov eax, DWORD PTR [rdi+120]
	and eax, 65535
	mov DWORD PTR [rdi+120], eax
	mov eax, 8127
	mov DWORD PTR [rdi+124], eax
	ldmxcsr DWORD PTR [rdi+124]
	lfence
	movabs rax, 1152921487695413247
	mov r10, QWORD PTR [rdi+24]
	and r10, rax
	movabs rax, 1152921487695413244
	mov r11, QWORD PTR [rdi+32]
	and r11, rax
	vmovq xmm5, r10
	vpbroadcastq ymm5, xmm5
	vmovq xmm6, r11
	vpbroadcastq ymm6, xmm6
	vpsrlq ymm9, ymm6, 40
	vpsllq ymm8, ymm6, 24
	vpsrlq ymm8, ymm8, 38
	vpsllq ymm7, ymm6, 50
	vpsrlq ymm7, ymm7, 38
	vpsrlq ymm10, ymm5, 52
	vpor ymm7, ymm7, ymm10
	vpsllq ymm6, ymm5, 12
	vpsrlq ymm6, ymm6, 38
	vpsllq ymm5, ymm5, 38
	vpsrlq ymm5, ymm5, 38
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm8
	vmovdqa ymm4, ymm9
	vpsllq ymm10, ymm0, 32
	vpor ymm11, ymm0, ymm10
	vpsllq ymm10, ymm1, 32
	vpor ymm12, ymm1, ymm10
	vpsllq ymm10, ymm2, 32
	vpor ymm13, ymm2, ymm10
	vpsllq ymm10, ymm3, 32
	vpor ymm14, ymm3, ymm10
	vpsllq ymm10, ymm4, 32
	vpor ymm15, ymm4, ymm10
	vpmuludq ymm5, ymm1, ymm15
	vpmuludq ymm10, ymm2, ymm14
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm3, ymm13
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm4, ymm12
	vpaddq ymm5, ymm5, ymm10
	vpsllq ymm10, ymm5, 2
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm0, ymm11
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm6, ymm2, ymm15
	vpmuludq ymm10, ymm3, ymm14
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm4, ymm13
	vpaddq ymm6, ymm6, ymm10
	vpsllq ymm10, ymm6, 2
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm0, ymm12
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm1, ymm11
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm7, ymm3, ymm15
	vpmuludq ymm10, ymm4, ymm14
	vpaddq ymm7, ymm7, ymm10
	vpsllq ymm10, ymm7, 2
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm0, ymm13
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm1, ymm12
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm2, ymm11
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm8, ymm4, ymm15
	vpsllq ymm10, ymm8, 2
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm0, ymm14
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm1, ymm13
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm2, ymm12
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm3, ymm11
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm9, ymm0, ymm15
	vpmuludq ymm10, ymm1, ymm14
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm2, ymm13
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm3, ymm12
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm4, ymm11
	vpaddq ymm9, ymm9, ymm10
	vmovq xmm4, r8
	vpbroadcastq ymm4, xmm4
	vpsrlq ymm10, ymm5, 26
	vpand ymm0, ymm5, ymm4
	vpaddq ymm6, ymm6, ymm10
	vpsrlq ymm10, ymm6, 26
	vpand ymm1, ymm6, ymm4
	vpaddq ymm7, ymm7, ymm10
	vpsrlq ymm10, ymm7, 26
	vpand ymm2, ymm7, ymm4
	vpaddq ymm8, ymm8, ymm10
	vpsrlq ymm10, ymm8, 26
	vpand ymm3, ymm8, ymm4
	vpaddq ymm9, ymm9, ymm10
	vpsrlq ymm10, ymm9, 26
	vmovdqa ymm5, ymm4
	vpand ymm4, ymm9, ymm4
	vpsllq ymm6, ymm10, 2
	vpaddq ymm10, ymm10, ymm6
	vpaddq ymm0, ymm0, ymm10
	vpsrlq ymm10, ymm0, 26
	vpand ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm10
	vpsllq ymm10, ymm0, 32
	vpblendd ymm11, ymm11, ymm10, 42
	vpsllq ymm10, ymm1, 32
	vpblendd ymm12, ymm12, ymm10, 42
	vpsllq ymm10, ymm2, 32
	vpblendd ymm13, ymm13, ymm10, 42
	vpsllq ymm10, ymm3, 32
	vpblendd ymm14, ymm14, ymm10, 42
	vpsllq ymm10, ymm4, 32
	vpblendd ymm15, ymm15, ymm10, 42
	vpmuludq ymm5, ymm1, ymm15
	vpmuludq ymm10, ymm2, ymm14
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm3, ymm13
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm4, ymm12
	vpaddq ymm5, ymm5, ymm10
	vpsllq ymm10, ymm5, 2
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm0, ymm11
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm6, ymm2, ymm15
	vpmuludq ymm10, ymm3, ymm14
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm4, ymm13
	vpaddq ymm6, ymm6, ymm10
	vpsllq ymm10, ymm6, 2
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm0, ymm12
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm1, ymm11
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm7, ymm3, ymm15
	vpmuludq ymm10, ymm4, ymm14
	vpaddq ymm7, ymm7, ymm10
	vpsllq ymm10, ymm7, 2
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm0, ymm13
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm1, ymm12
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm2, ymm11
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm8, ymm4, ymm15
	vpsllq ymm10, ymm8, 2
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm0, ymm14
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm1, ymm13
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm2, ymm12
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm3, ymm11
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm9, ymm0, ymm15
	vpmuludq ymm10, ymm1, ymm14
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm2, ymm13
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm3, ymm12
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm4, ymm11
	vpaddq ymm9, ymm9, ymm10
	vmovq xmm4, r8
	vpbroadcastq ymm4, xmm4
	vpsrlq ymm10, ymm5, 26
	vpand ymm0, ymm5, ymm4
	vpaddq ymm6, ymm6, ymm10
	vpsrlq ymm10, ymm6, 26
	vpand ymm1, ymm6, ymm4
	vpaddq ymm7, ymm7, ymm10
	vpsrlq ymm10, ymm7, 26
	vpand ymm2, ymm7, ymm4
	vpaddq ymm8, ymm8, ymm10
	vpsrlq ymm10, ymm8, 26
	vpand ymm3, ymm8, ymm4
	vpaddq ymm9, ymm9, ymm10
	vpsrlq ymm10, ymm9, 26
	vmovdqa ymm5, ymm4
	vpand ymm4, ymm9, ymm4
	vpsllq ymm6, ymm10, 2
	vpaddq ymm10, ymm10, ymm6
	vpaddq ymm0, ymm0, ymm10
	vpsrlq ymm10, ymm0, 26
	vpand ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm10
	vpsllq ymm10, ymm0, 32
	vpblendd ymm11, ymm11, ymm10, 10
	vpsllq ymm10, ymm1, 32
	vpblendd ymm12, ymm12, ymm10, 10
	vpsllq ymm10, ymm2, 32
	vpblendd ymm13, ymm13, ymm10, 10
	vpsllq ymm10, ymm3, 32
	vpblendd ymm14, ymm14, ymm10, 10
	vpsllq ymm10, ymm4, 32
	vpblendd ymm15, ymm15, ymm10, 10
	vpmuludq ymm5, ymm1, ymm15
	vpmuludq ymm10, ymm2, ymm14
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm3, ymm13
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm4, ymm12
	vpaddq ymm5, ymm5, ymm10
	vpsllq ymm10, ymm5, 2
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm0, ymm11
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm6, ymm2, ymm15
	vpmuludq ymm10, ymm3, ymm14
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm4, ymm13
	vpaddq ymm6, ymm6, ymm10
	vpsllq ymm10, ymm6, 2
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm0, ymm12
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm1, ymm11
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm7, ymm3, ymm15
	vpmuludq ymm10, ymm4, ymm14
	vpaddq ymm7, ymm7, ymm10
	vpsllq ymm10, ymm7, 2
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm0, ymm13
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm1, ymm12
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm2, ymm11
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm8, ymm4, ymm15
	vpsllq ymm10, ymm8, 2
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm0, ymm14
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm1, ymm13
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm2, ymm12
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm3, ymm11
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm9, ymm0, ymm15
	vpmuludq ymm10, ymm1, ymm14
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm2, ymm13
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm3, ymm12
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm4, ymm11
	vpaddq ymm9, ymm9, ymm10
	vmovq xmm4, r8
	vpbroadcastq ymm4, xmm4
	vpsrlq ymm10, ymm5, 26
	vpand ymm0, ymm5, ymm4
	vpaddq ymm6, ymm6, ymm10
	vpsrlq ymm10, ymm6, 26
	vpand ymm1, ymm6, ymm4
	vpaddq ymm7, ymm7, ymm10
	vpsrlq ymm10, ymm7, 26
	vpand ymm2, ymm7, ymm4
	vpaddq ymm8, ymm8, ymm10
	vpsrlq ymm10, ymm8, 26
	vpand ymm3, ymm8, ymm4
	vpaddq ymm9, ymm9, ymm10
	vpsrlq ymm10, ymm9, 26
	vmovdqa ymm5, ymm4
	vpand ymm4, ymm9, ymm4
	vpsllq ymm6, ymm10, 2
	vpaddq ymm10, ymm10, ymm6
	vpaddq ymm0, ymm0, ymm10
	vpsrlq ymm10, ymm0, 26
	vpand ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm10
	vpsllq ymm10, ymm0, 32
	vpor ymm10, ymm10, ymm0
	vpblendd ymm11, ymm11, ymm10, 87
	vpsllq ymm10, ymm1, 32
	vpor ymm10, ymm10, ymm1
	vpblendd ymm12, ymm12, ymm10, 87
	vpsllq ymm10, ymm2, 32
	vpor ymm10, ymm10, ymm2
	vpblendd ymm13, ymm13, ymm10, 87
	vpsllq ymm10, ymm3, 32
	vpor ymm10, ymm10, ymm3
	vpblendd ymm14, ymm14, ymm10, 87
	vpsllq ymm10, ymm4, 32
	vpor ymm10, ymm10, ymm4
	vpblendd ymm15, ymm15, ymm10, 87
	mov r10, QWORD PTR [rdi]
	mov r11, QWORD PTR [rdi+8]
	mov rax, QWORD PTR [rdi+16]
	vmovq xmm5, r10
	vmovq xmm6, r11
	vpsrlq ymm9, ymm6, 40
	vpsllq ymm8, ymm6, 24
	vpsrlq ymm8, ymm8, 38
	vpsllq ymm7, ymm6, 50
	vpsrlq ymm7, ymm7, 38
	vpsrlq ymm10, ymm5, 52
	vpor ymm7, ymm7, ymm10
	vpsllq ymm6, ymm5, 12
	vpsrlq ymm6, ymm6, 38
	vpsllq ymm5, ymm5, 38
	vpsrlq ymm5, ymm5, 38
	vmovq xmm10, rax
	vpsllq ymm10, ymm10, 24
	vpor ymm9, ymm9, ymm10
	vmovdqa ymm0, ymm5
	vmovdqa ymm1, ymm6
	vmovdqa ymm2, ymm7
	vmovdqa ymm3, ymm8
	vmovdqa ymm4, ymm9
	mov rcx, rdx
	shr rcx, 2
	sub rcx, 1
22:
	vmovdqu ymm7, YMMWORD PTR [rsi]
	vmovdqu ymm8, YMMWORD PTR [rsi+32]
	vpunpcklqdq ymm5, ymm7, ymm8
	vpunpckhqdq ymm6, ymm7, ymm8
	vpermq ymm5, ymm5, 216
	vpermq ymm6, ymm6, 216
	vpsrlq ymm9, ymm6, 40
	vpsllq ymm8, ymm6, 24
	vpsrlq ymm8, ymm8, 38
	vpsllq ymm7, ymm6, 50
	vpsrlq ymm7, ymm7, 38
	vpsrlq ymm10, ymm5, 52
	vpor ymm7, ymm7, ymm10
	vpsllq ymm6, ymm5, 12
	vpsrlq ymm6, ymm6, 38
	vpsllq ymm5, ymm5, 38
	vpsrlq ymm5, ymm5, 38
	vmovq xmm10, r9
	vpbroadcastq ymm10, xmm10
	vpor ymm9, ymm9, ymm10
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm6
	vpaddq ymm2, ymm2, ymm7
	vpaddq ymm3, ymm3, ymm8
	vpaddq ymm4, ymm4, ymm9
	vpmuludq ymm5, ymm1, ymm15
	vpmuludq ymm10, ymm2, ymm14
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm3, ymm13
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm4, ymm12
	vpaddq ymm5, ymm5, ymm10
	vpsllq ymm10, ymm5, 2
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm0, ymm11
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm6, ymm2, ymm15
	vpmuludq ymm10, ymm3, ymm14
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm4, ymm13
	vpaddq ymm6, ymm6, ymm10
	vpsllq ymm10, ymm6, 2
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm0, ymm12
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm1, ymm11
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm7, ymm3, ymm15
	vpmuludq ymm10, ymm4, ymm14
	vpaddq ymm7, ymm7, ymm10
	vpsllq ymm10, ymm7, 2
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm0, ymm13
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm1, ymm12
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm2, ymm11
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm8, ymm4, ymm15
	vpsllq ymm10, ymm8, 2
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm0, ymm14
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm1, ymm13
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm2, ymm12
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm3, ymm11
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm9, ymm0, ymm15
	vpmuludq ymm10, ymm1, ymm14
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm2, ymm13
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm3, ymm12
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm4, ymm11
	vpaddq ymm9, ymm9, ymm10
	vmovq xmm4, r8
	vpbroadcastq ymm4, xmm4
	vpsrlq ymm10, ymm5, 26
	vpand ymm0, ymm5, ymm4
	vpaddq ymm6, ymm6, ymm10
	vpsrlq ymm10, ymm6, 26
	vpand ymm1, ymm6, ymm4
	vpaddq ymm7, ymm7, ymm10
	vpsrlq ymm10, ymm7, 26
	vpand ymm2, ymm7, ymm4
	vpaddq ymm8, ymm8, ymm10
	vpsrlq ymm10, ymm8, 26
	vpand ymm3, ymm8, ymm4
	vpaddq ymm9, ymm9, ymm10
	vpsrlq ymm10, ymm9, 26
	vmovdqa ymm5, ymm4
	vpand ymm4, ymm9, ymm4
	vpsllq ymm6, ymm10, 2
	vpaddq ymm10, ymm10, ymm6
	vpaddq ymm0, ymm0, ymm10
	vpsrlq ymm10, ymm0, 26
	vpand ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm10
	add rsi, 64
	sub rcx, 1
	jne 22b
	mov eax, 5
	mov r10d, 134217727
	vmovdqu ymm7, YMMWORD PTR [rsi]
	vmovdqu ymm8, YMMWORD PTR [rsi+32]
	vpunpcklqdq ymm5, ymm7, ymm8
	vpunpckhqdq ymm6, ymm7, ymm8
	vpermq ymm5, ymm5, 216
	vpermq ymm6, ymm6, 216
	vpsrlq ymm9, ymm6, 40
	vpsllq ymm8, ymm6, 24
	vpsrlq ymm8, ymm8, 38
	vpsllq ymm7, ymm6, 50
	vpsrlq ymm7, ymm7, 38
	vpsrlq ymm10, ymm5, 52
	vpor ymm7, ymm7, ymm10
	vpsllq ymm6, ymm5, 12
	vpsrlq ymm6, ymm6, 38
	vpsllq ymm5, ymm5, 38
	vpsrlq ymm5, ymm5, 38
	vmovq xmm10, r9
	vpbroadcastq ymm10, xmm10
	vpor ymm9, ymm9, ymm10
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm6
	vpaddq ymm2, ymm2, ymm7
	vpaddq ymm3, ymm3, ymm8
	vpaddq ymm4, ymm4, ymm9
	vpsrlq ymm11, ymm11, 32
	vpsrlq ymm12, ymm12, 32
	vpsrlq ymm13, ymm13, 32
	vpsrlq ymm14, ymm14, 32
	vpsrlq ymm15, ymm15, 32
	vpmuludq ymm5, ymm1, ymm15
	vpmuludq ymm10, ymm2, ymm14
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm3, ymm13
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm4, ymm12
	vpaddq ymm5, ymm5, ymm10
	vpsllq ymm10, ymm5, 2
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm10, ymm0, ymm11
	vpaddq ymm5, ymm5, ymm10
	vpmuludq ymm6, ymm2, ymm15
	vpmuludq ymm10, ymm3, ymm14
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm4, ymm13
	vpaddq ymm6, ymm6, ymm10
	vpsllq ymm10, ymm6, 2
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm0, ymm12
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm10, ymm1, ymm11
	vpaddq ymm6, ymm6, ymm10
	vpmuludq ymm7, ymm3, ymm15
	vpmuludq ymm10, ymm4, ymm14
	vpaddq ymm7, ymm7, ymm10
	vpsllq ymm10, ymm7, 2
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm0, ymm13
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm1, ymm12
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm10, ymm2, ymm11
	vpaddq ymm7, ymm7, ymm10
	vpmuludq ymm8, ymm4, ymm15
	vpsllq ymm10, ymm8, 2
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm0, ymm14
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm1, ymm13
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm2, ymm12
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm10, ymm3, ymm11
	vpaddq ymm8, ymm8, ymm10
	vpmuludq ymm9, ymm0, ymm15
	vpmuludq ymm10, ymm1, ymm14
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm2, ymm13
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm3, ymm12
	vpaddq ymm9, ymm9, ymm10
	vpmuludq ymm10, ymm4, ymm11
	vpaddq ymm9, ymm9, ymm10
	vmovq xmm4, r8
	vpbroadcastq ymm4, xmm4
	vpsrlq ymm10, ymm5, 26
	vpand ymm0, ymm5, ymm4
	vpaddq ymm6, ymm6, ymm10
	vpsrlq ymm10, ymm6, 26
	vpand ymm1, ymm6, ymm4
	vpaddq ymm7, ymm7, ymm10
	vpsrlq ymm10, ymm7, 26
	vpand ymm2, ymm7, ymm4
	vpaddq ymm8, ymm8, ymm10
	vpsrlq ymm10, ymm8, 26
	vpand ymm3, ymm8, ymm4
	vpaddq ymm9, ymm9, ymm10
	vpsrlq ymm10, ymm9, 26
	vmovdqa ymm5, ymm4
	vpand ymm4, ymm9, ymm4
	vpsllq ymm6, ymm10, 2
	vpaddq ymm10, ymm10, ymm6
	vpaddq ymm0, ymm0, ymm10
	vpsrlq ymm10, ymm0, 26
	vpand ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm10
	vpermq ymm10, ymm0, 78
	vpaddq ymm5, ymm0, ymm10
	vpunpckhqdq ymm10, ymm5, ymm5
	vpaddq ymm5, ymm5, ymm10
	vpermq ymm10, ymm1, 78
	vpaddq ymm6, ymm1, ymm10
	vpunpckhqdq ymm10, ymm6, ymm6
	vpaddq ymm6, ymm6, ymm10
	vpermq ymm10, ymm2, 78
	vpaddq ymm7, ymm2, ymm10
	vpunpckhqdq ymm10, ymm7, ymm7
	vpaddq ymm7, ymm7, ymm10
	vpermq ymm10, ymm3, 78
	vpaddq ymm8, ymm3, ymm10
	vpunpckhqdq ymm10, ymm8, ymm8
	vpaddq ymm8, ymm8, ymm10
	vpermq ymm10, ymm4, 78
	vpaddq ymm9, ymm4, ymm10
	vpunpckhqdq ymm10, ymm9, ymm9
	vpaddq ymm9, ymm9, ymm10
	vmovq xmm4, r8
	vpbroadcastq ymm4, xmm4
	vpsrlq ymm10, ymm5, 26
	vpand ymm0, ymm5, ymm4
	vpaddq ymm6, ymm6, ymm10
	vpsrlq ymm10, ymm6, 26
	vpand ymm1, ymm6, ymm4
	vpaddq ymm7, ymm7, ymm10
	vpsrlq ymm10, ymm7, 26
	vpand ymm2, ymm7, ymm4
	vpaddq ymm8, ymm8, ymm10
	vpsrlq ymm10, ymm8, 26
	vpand ymm3, ymm8, ymm4
	vpaddq ymm9, ymm9, ymm10
	vpsrlq ymm10, ymm9, 26
	vmovdqa ymm5, ymm4
	vpand ymm4, ymm9, ymm4
	vpsllq ymm6, ymm10, 2
	vpaddq ymm10, ymm10, ymm6
	vpaddq ymm0, ymm0, ymm10
	vpsrlq ymm10, ymm0, 26
	vpand ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm10
	vmovq xmm5, r8
	vpbroadcastq ymm5, xmm5
	vpsrlq ymm10, ymm1, 26
	vpand ymm1, ymm1, ymm5
	vpaddq ymm2, ymm2, ymm10
	vpsrlq ymm10, ymm2, 26
	vpand ymm2, ymm2, ymm5
	vpaddq ymm3, ymm3, ymm10
	vpsrlq ymm10, ymm3, 26
	vpand ymm3, ymm3, ymm5
	vpaddq ymm4, ymm4, ymm10
	vmovq xmm10, rax
	vpbroadcastq ymm10, xmm10
	vpaddq ymm11, ymm0, ymm10
	vpsrlq ymm10, ymm11, 26
	vpand ymm11, ymm11, ymm5
	vpaddq ymm12, ymm1, ymm10
	vpsrlq ymm10, ymm12, 26
	vpand ymm12, ymm12, ymm5
	vpaddq ymm13, ymm2, ymm10
	vpsrlq ymm10, ymm13, 26
	vpand ymm13, ymm13, ymm5
	vpaddq ymm14, ymm3, ymm10
	vpsrlq ymm10, ymm14, 26
	vpand ymm14, ymm14, ymm5
	vpaddq ymm15, ymm4, ymm10
	vpsrlq ymm10, ymm15, 26
	vpand ymm15, ymm15, ymm5
	vmovq xmm6, r10
	vpbroadcastq ymm6, xmm6
	vpmuludq ymm10, ymm10, ymm6
	vpand ymm11, ymm11, ymm10
	vpandn ymm0, ymm10, ymm0
	vpor ymm0, ymm0, ymm11
	vpand ymm12, ymm12, ymm10
	vpandn ymm1, ymm10, ymm1
	vpor ymm1, ymm1, ymm12
	vpand ymm13, ymm13, ymm10
	vpandn ymm2, ymm10, ymm2
	vpor ymm2, ymm2, ymm13
	vpand ymm14, ymm14, ymm10
	vpandn ymm3, ymm10, ymm3
	vpor ymm3, ymm3, ymm14
	vpand ymm15, ymm15, ymm10
	vpandn ymm4, ymm10, ymm4
	vpor ymm4, ymm4, ymm15
	lfence
	ldmxcsr DWORD PTR [rdi+120]
	vpsllq ymm6, ymm1, 26
	vpsllq ymm7, ymm2, 52
	vpor ymm6, ymm6, ymm0
	vpor ymm6, ymm6, ymm7
	vpsrlq ymm7, ymm2, 12
	vpsllq ymm8, ymm3, 14
	vpor ymm7, ymm7, ymm8
	vpsllq ymm8, ymm4, 40
	vpor ymm7, ymm7, ymm8
	vpsrlq ymm8, ymm4, 24
	vpunpcklqdq ymm10, ymm6, ymm7
	vmovdqu XMMWORD PTR [rdi], xmm10
	vpunpcklqdq ymm10, ymm7, ymm8
	vmovdqu XMMWORD PTR [rdi+8], xmm10
	vzeroupper
	add rsi, 64
	and rdx, 3
	test rdx, rdx
	je 23f
	call {vg_poly1305_blocks}
	jmp 24f
23:
24:
	jmp 21f
20:
	call {vg_poly1305_blocks}
21:
	ret
	.p2align 6
