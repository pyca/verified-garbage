// The functions of `src/internal/vg_poly1305_blocks_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_blocks_avx512:
	cmp rdx, 40
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
	mov eax, 1
	vmovq xmm5, r10
	vpbroadcastq zmm5, xmm5
	vmovq xmm6, r11
	vpbroadcastq zmm6, xmm6
	vpsrlq zmm9, zmm6, 40
	vpsllq zmm8, zmm6, 24
	vpsrlq zmm8, zmm8, 38
	vpsllq zmm7, zmm6, 50
	vpsrlq zmm7, zmm7, 38
	vpsrlq zmm10, zmm5, 52
	vporq zmm7, zmm7, zmm10
	vpsllq zmm6, zmm5, 12
	vpsrlq zmm6, zmm6, 38
	vpsllq zmm5, zmm5, 38
	vpsrlq zmm5, zmm5, 38
	vmovdqa64 zmm0, zmm5
	vmovdqa64 zmm1, zmm6
	vmovdqa64 zmm2, zmm7
	vmovdqa64 zmm3, zmm8
	vmovdqa64 zmm4, zmm9
	vpsllq zmm10, zmm0, 32
	vporq zmm11, zmm0, zmm10
	vpsllq zmm10, zmm1, 32
	vporq zmm12, zmm1, zmm10
	vpsllq zmm10, zmm2, 32
	vporq zmm13, zmm2, zmm10
	vpsllq zmm10, zmm3, 32
	vporq zmm14, zmm3, zmm10
	vpsllq zmm10, zmm4, 32
	vporq zmm15, zmm4, zmm10
	vpmuludq zmm5, zmm1, zmm15
	vpmuludq zmm10, zmm2, zmm14
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm3, zmm13
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm4, zmm12
	vpaddq zmm5, zmm5, zmm10
	vpsllq zmm10, zmm5, 2
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm0, zmm11
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm6, zmm2, zmm15
	vpmuludq zmm10, zmm3, zmm14
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm4, zmm13
	vpaddq zmm6, zmm6, zmm10
	vpsllq zmm10, zmm6, 2
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm0, zmm12
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm1, zmm11
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm7, zmm3, zmm15
	vpmuludq zmm10, zmm4, zmm14
	vpaddq zmm7, zmm7, zmm10
	vpsllq zmm10, zmm7, 2
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm0, zmm13
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm1, zmm12
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm2, zmm11
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm8, zmm4, zmm15
	vpsllq zmm10, zmm8, 2
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm0, zmm14
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm1, zmm13
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm2, zmm12
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm3, zmm11
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm9, zmm0, zmm15
	vpmuludq zmm10, zmm1, zmm14
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm2, zmm13
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm3, zmm12
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm4, zmm11
	vpaddq zmm9, zmm9, zmm10
	vmovq xmm4, r8
	vpbroadcastq zmm4, xmm4
	vpsrlq zmm10, zmm5, 26
	vpandq zmm0, zmm5, zmm4
	vpaddq zmm6, zmm6, zmm10
	vpsrlq zmm10, zmm6, 26
	vpandq zmm1, zmm6, zmm4
	vpaddq zmm7, zmm7, zmm10
	vpsrlq zmm10, zmm7, 26
	vpandq zmm2, zmm7, zmm4
	vpaddq zmm8, zmm8, zmm10
	vpsrlq zmm10, zmm8, 26
	vpandq zmm3, zmm8, zmm4
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm9, 26
	vmovdqa64 zmm5, zmm4
	vpandq zmm4, zmm9, zmm4
	vpsllq zmm6, zmm10, 2
	vpaddq zmm10, zmm10, zmm6
	vpaddq zmm0, zmm0, zmm10
	vpsrlq zmm10, zmm0, 26
	vpandq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm10
	vpsrlq zmm5, zmm11, 32
	vmovdqa64 zmm11, zmm0
	vpunpcklqdq zmm0, zmm0, zmm5
	vpsrlq zmm6, zmm12, 32
	vmovdqa64 zmm12, zmm1
	vpunpcklqdq zmm1, zmm1, zmm6
	vpsrlq zmm7, zmm13, 32
	vmovdqa64 zmm13, zmm2
	vpunpcklqdq zmm2, zmm2, zmm7
	vpsrlq zmm8, zmm14, 32
	vmovdqa64 zmm14, zmm3
	vpunpcklqdq zmm3, zmm3, zmm8
	vpsrlq zmm9, zmm15, 32
	vmovdqa64 zmm15, zmm4
	vpunpcklqdq zmm4, zmm4, zmm9
	vpmuludq zmm5, zmm1, zmm15
	vpmuludq zmm10, zmm2, zmm14
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm3, zmm13
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm4, zmm12
	vpaddq zmm5, zmm5, zmm10
	vpsllq zmm10, zmm5, 2
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm0, zmm11
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm6, zmm2, zmm15
	vpmuludq zmm10, zmm3, zmm14
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm4, zmm13
	vpaddq zmm6, zmm6, zmm10
	vpsllq zmm10, zmm6, 2
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm0, zmm12
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm1, zmm11
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm7, zmm3, zmm15
	vpmuludq zmm10, zmm4, zmm14
	vpaddq zmm7, zmm7, zmm10
	vpsllq zmm10, zmm7, 2
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm0, zmm13
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm1, zmm12
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm2, zmm11
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm8, zmm4, zmm15
	vpsllq zmm10, zmm8, 2
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm0, zmm14
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm1, zmm13
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm2, zmm12
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm3, zmm11
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm9, zmm0, zmm15
	vpmuludq zmm10, zmm1, zmm14
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm2, zmm13
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm3, zmm12
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm4, zmm11
	vpaddq zmm9, zmm9, zmm10
	vmovq xmm4, r8
	vpbroadcastq zmm4, xmm4
	vpsrlq zmm10, zmm5, 26
	vpandq zmm0, zmm5, zmm4
	vpaddq zmm6, zmm6, zmm10
	vpsrlq zmm10, zmm6, 26
	vpandq zmm1, zmm6, zmm4
	vpaddq zmm7, zmm7, zmm10
	vpsrlq zmm10, zmm7, 26
	vpandq zmm2, zmm7, zmm4
	vpaddq zmm8, zmm8, zmm10
	vpsrlq zmm10, zmm8, 26
	vpandq zmm3, zmm8, zmm4
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm9, 26
	vmovdqa64 zmm5, zmm4
	vpandq zmm4, zmm9, zmm4
	vpsllq zmm6, zmm10, 2
	vpaddq zmm10, zmm10, zmm6
	vpaddq zmm0, zmm0, zmm10
	vpsrlq zmm10, zmm0, 26
	vpandq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm10
	vmovq xmm5, r10
	vpbroadcastq zmm5, xmm5
	vmovq xmm6, r11
	vpbroadcastq zmm6, xmm6
	vpsrlq zmm9, zmm6, 40
	vpsllq zmm8, zmm6, 24
	vpsrlq zmm8, zmm8, 38
	vpsllq zmm7, zmm6, 50
	vpsrlq zmm7, zmm7, 38
	vpsrlq zmm10, zmm5, 52
	vporq zmm7, zmm7, zmm10
	vpsllq zmm6, zmm5, 12
	vpsrlq zmm6, zmm6, 38
	vpsllq zmm5, zmm5, 38
	vpsrlq zmm5, zmm5, 38
	vpunpcklqdq zmm11, zmm11, zmm5
	vpunpcklqdq zmm5, zmm0, zmm0
	vpunpckhqdq zmm10, zmm0, zmm0
	vshufi32x4 zmm0, zmm5, zmm10, 0
	vpunpcklqdq zmm5, zmm11, zmm11
	vpunpckhqdq zmm10, zmm11, zmm11
	vshufi32x4 zmm11, zmm5, zmm10, 0
	vshufi32x4 zmm0, zmm0, zmm11, 136
	vpunpcklqdq zmm12, zmm12, zmm6
	vpunpcklqdq zmm6, zmm1, zmm1
	vpunpckhqdq zmm10, zmm1, zmm1
	vshufi32x4 zmm1, zmm6, zmm10, 0
	vpunpcklqdq zmm6, zmm12, zmm12
	vpunpckhqdq zmm10, zmm12, zmm12
	vshufi32x4 zmm12, zmm6, zmm10, 0
	vshufi32x4 zmm1, zmm1, zmm12, 136
	vpunpcklqdq zmm13, zmm13, zmm7
	vpunpcklqdq zmm7, zmm2, zmm2
	vpunpckhqdq zmm10, zmm2, zmm2
	vshufi32x4 zmm2, zmm7, zmm10, 0
	vpunpcklqdq zmm7, zmm13, zmm13
	vpunpckhqdq zmm10, zmm13, zmm13
	vshufi32x4 zmm13, zmm7, zmm10, 0
	vshufi32x4 zmm2, zmm2, zmm13, 136
	vpunpcklqdq zmm14, zmm14, zmm8
	vpunpcklqdq zmm8, zmm3, zmm3
	vpunpckhqdq zmm10, zmm3, zmm3
	vshufi32x4 zmm3, zmm8, zmm10, 0
	vpunpcklqdq zmm8, zmm14, zmm14
	vpunpckhqdq zmm10, zmm14, zmm14
	vshufi32x4 zmm14, zmm8, zmm10, 0
	vshufi32x4 zmm3, zmm3, zmm14, 136
	vpunpcklqdq zmm15, zmm15, zmm9
	vpunpcklqdq zmm9, zmm4, zmm4
	vpunpckhqdq zmm10, zmm4, zmm4
	vshufi32x4 zmm4, zmm9, zmm10, 0
	vpunpcklqdq zmm9, zmm15, zmm15
	vpunpckhqdq zmm10, zmm15, zmm15
	vshufi32x4 zmm15, zmm9, zmm10, 0
	vshufi32x4 zmm4, zmm4, zmm15, 136
	vmovq xmm10, rax
	vpbroadcastq zmm10, xmm10
	vpbroadcastq zmm11, xmm0
	vpunpcklqdq zmm11, zmm11, zmm10
	vpandnq zmm10, zmm10, zmm10
	vpbroadcastq zmm12, xmm1
	vpunpcklqdq zmm12, zmm12, zmm10
	vpbroadcastq zmm13, xmm2
	vpunpcklqdq zmm13, zmm13, zmm10
	vpbroadcastq zmm14, xmm3
	vpunpcklqdq zmm14, zmm14, zmm10
	vpbroadcastq zmm15, xmm4
	vpunpcklqdq zmm15, zmm15, zmm10
	vpmuludq zmm5, zmm1, zmm15
	vpmuludq zmm10, zmm2, zmm14
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm3, zmm13
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm4, zmm12
	vpaddq zmm5, zmm5, zmm10
	vpsllq zmm10, zmm5, 2
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm0, zmm11
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm6, zmm2, zmm15
	vpmuludq zmm10, zmm3, zmm14
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm4, zmm13
	vpaddq zmm6, zmm6, zmm10
	vpsllq zmm10, zmm6, 2
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm0, zmm12
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm1, zmm11
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm7, zmm3, zmm15
	vpmuludq zmm10, zmm4, zmm14
	vpaddq zmm7, zmm7, zmm10
	vpsllq zmm10, zmm7, 2
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm0, zmm13
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm1, zmm12
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm2, zmm11
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm8, zmm4, zmm15
	vpsllq zmm10, zmm8, 2
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm0, zmm14
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm1, zmm13
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm2, zmm12
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm3, zmm11
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm9, zmm0, zmm15
	vpmuludq zmm10, zmm1, zmm14
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm2, zmm13
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm3, zmm12
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm4, zmm11
	vpaddq zmm9, zmm9, zmm10
	vmovq xmm4, r8
	vpbroadcastq zmm4, xmm4
	vpsrlq zmm10, zmm5, 26
	vpandq zmm0, zmm5, zmm4
	vpaddq zmm6, zmm6, zmm10
	vpsrlq zmm10, zmm6, 26
	vpandq zmm1, zmm6, zmm4
	vpaddq zmm7, zmm7, zmm10
	vpsrlq zmm10, zmm7, 26
	vpandq zmm2, zmm7, zmm4
	vpaddq zmm8, zmm8, zmm10
	vpsrlq zmm10, zmm8, 26
	vpandq zmm3, zmm8, zmm4
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm9, 26
	vmovdqa64 zmm5, zmm4
	vpandq zmm4, zmm9, zmm4
	vpsllq zmm6, zmm10, 2
	vpaddq zmm10, zmm10, zmm6
	vpaddq zmm0, zmm0, zmm10
	vpsrlq zmm10, zmm0, 26
	vpandq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm10
	vpbroadcastq zmm10, xmm0
	vpsllq zmm5, zmm0, 32
	vporq zmm11, zmm5, zmm10
	vpbroadcastq zmm10, xmm1
	vpsllq zmm6, zmm1, 32
	vporq zmm12, zmm6, zmm10
	vpbroadcastq zmm10, xmm2
	vpsllq zmm7, zmm2, 32
	vporq zmm13, zmm7, zmm10
	vpbroadcastq zmm10, xmm3
	vpsllq zmm8, zmm3, 32
	vporq zmm14, zmm8, zmm10
	vpbroadcastq zmm10, xmm4
	vpsllq zmm9, zmm4, 32
	vporq zmm15, zmm9, zmm10
	mov r10, QWORD PTR [rdi]
	mov r11, QWORD PTR [rdi+8]
	mov rax, QWORD PTR [rdi+16]
	vmovq xmm5, r10
	vmovq xmm6, r11
	vpsrlq zmm9, zmm6, 40
	vpsllq zmm8, zmm6, 24
	vpsrlq zmm8, zmm8, 38
	vpsllq zmm7, zmm6, 50
	vpsrlq zmm7, zmm7, 38
	vpsrlq zmm10, zmm5, 52
	vporq zmm7, zmm7, zmm10
	vpsllq zmm6, zmm5, 12
	vpsrlq zmm6, zmm6, 38
	vpsllq zmm5, zmm5, 38
	vpsrlq zmm5, zmm5, 38
	vmovq xmm10, rax
	vpsllq zmm10, zmm10, 24
	vporq zmm9, zmm9, zmm10
	vmovdqa64 zmm0, zmm5
	vmovdqa64 zmm1, zmm6
	vmovdqa64 zmm2, zmm7
	vmovdqa64 zmm3, zmm8
	vmovdqa64 zmm4, zmm9
	vpsllq zmm5, zmm12, 2
	vpaddq zmm5, zmm5, zmm12
	vpsllq zmm6, zmm13, 2
	vpaddq zmm6, zmm6, zmm13
	vpsllq zmm7, zmm14, 2
	vpaddq zmm7, zmm7, zmm14
	vpsllq zmm8, zmm15, 2
	vpaddq zmm8, zmm8, zmm15
	vmovdqu XMMWORD PTR [rdi+56], xmm11
	vmovdqu XMMWORD PTR [rdi+60], xmm12
	vmovdqu XMMWORD PTR [rdi+64], xmm13
	vmovdqu XMMWORD PTR [rdi+68], xmm14
	vmovdqu XMMWORD PTR [rdi+72], xmm15
	vmovdqu XMMWORD PTR [rdi+76], xmm5
	vmovdqu XMMWORD PTR [rdi+80], xmm6
	vmovdqu XMMWORD PTR [rdi+84], xmm7
	vmovdqu XMMWORD PTR [rdi+88], xmm8
	mov QWORD PTR [rdi+104], r8
	mov QWORD PTR [rdi+112], r9
	mov rcx, rdx
	shr rcx, 3
	sub rcx, 1
22:
	vmovdqu32 zmm7, ZMMWORD PTR [rsi]
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+64]
	vpunpcklqdq zmm5, zmm7, zmm8
	vpunpckhqdq zmm6, zmm7, zmm8
	vpsrlq zmm9, zmm6, 40
	vpsllq zmm8, zmm6, 24
	vpsrlq zmm8, zmm8, 38
	vpsllq zmm7, zmm6, 50
	vpsrlq zmm7, zmm7, 38
	vpsrlq zmm10, zmm5, 52
	vporq zmm7, zmm7, zmm10
	vpsllq zmm6, zmm5, 12
	vpsrlq zmm6, zmm6, 38
	vpsllq zmm5, zmm5, 38
	vpsrlq zmm5, zmm5, 38
	vporq zmm9, zmm9, QWORD PTR [rdi+112]{1to8}
	vpaddq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm6
	vpaddq zmm2, zmm2, zmm7
	vpaddq zmm3, zmm3, zmm8
	vpaddq zmm4, zmm4, zmm9
	vpmuludq zmm5, zmm0, QWORD PTR [rdi+56]{1to8}
	vpmuludq zmm10, zmm1, QWORD PTR [rdi+88]{1to8}
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm2, QWORD PTR [rdi+84]{1to8}
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm3, QWORD PTR [rdi+80]{1to8}
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm4, QWORD PTR [rdi+76]{1to8}
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm6, zmm0, QWORD PTR [rdi+60]{1to8}
	vpmuludq zmm10, zmm1, QWORD PTR [rdi+56]{1to8}
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm2, QWORD PTR [rdi+88]{1to8}
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm3, QWORD PTR [rdi+84]{1to8}
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm4, QWORD PTR [rdi+80]{1to8}
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm7, zmm0, QWORD PTR [rdi+64]{1to8}
	vpmuludq zmm10, zmm1, QWORD PTR [rdi+60]{1to8}
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm2, QWORD PTR [rdi+56]{1to8}
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm3, QWORD PTR [rdi+88]{1to8}
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm4, QWORD PTR [rdi+84]{1to8}
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm8, zmm0, QWORD PTR [rdi+68]{1to8}
	vpmuludq zmm10, zmm1, QWORD PTR [rdi+64]{1to8}
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm2, QWORD PTR [rdi+60]{1to8}
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm3, QWORD PTR [rdi+56]{1to8}
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm4, QWORD PTR [rdi+88]{1to8}
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm9, zmm0, QWORD PTR [rdi+72]{1to8}
	vpmuludq zmm10, zmm1, QWORD PTR [rdi+68]{1to8}
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm2, QWORD PTR [rdi+64]{1to8}
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm3, QWORD PTR [rdi+60]{1to8}
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm4, QWORD PTR [rdi+56]{1to8}
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm5, 26
	vpandq zmm0, zmm5, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm6, zmm6, zmm10
	vpsrlq zmm10, zmm6, 26
	vpandq zmm1, zmm6, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm7, zmm7, zmm10
	vpsrlq zmm10, zmm7, 26
	vpandq zmm2, zmm7, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm8, zmm8, zmm10
	vpsrlq zmm10, zmm8, 26
	vpandq zmm3, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm9, 26
	vpandq zmm4, zmm9, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm6, zmm10, 2
	vpaddq zmm10, zmm10, zmm6
	vpaddq zmm0, zmm0, zmm10
	vpsrlq zmm10, zmm0, 26
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm10
	add rsi, 128
	sub rcx, 1
	jne 22b
	mov eax, 5
	mov r10d, 134217727
	vmovdqu32 zmm7, ZMMWORD PTR [rsi]
	vmovdqu32 zmm8, ZMMWORD PTR [rsi+64]
	vpunpcklqdq zmm5, zmm7, zmm8
	vpunpckhqdq zmm6, zmm7, zmm8
	vpsrlq zmm9, zmm6, 40
	vpsllq zmm8, zmm6, 24
	vpsrlq zmm8, zmm8, 38
	vpsllq zmm7, zmm6, 50
	vpsrlq zmm7, zmm7, 38
	vpsrlq zmm10, zmm5, 52
	vporq zmm7, zmm7, zmm10
	vpsllq zmm6, zmm5, 12
	vpsrlq zmm6, zmm6, 38
	vpsllq zmm5, zmm5, 38
	vpsrlq zmm5, zmm5, 38
	vmovq xmm10, r9
	vpbroadcastq zmm10, xmm10
	vporq zmm9, zmm9, zmm10
	vpaddq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm6
	vpaddq zmm2, zmm2, zmm7
	vpaddq zmm3, zmm3, zmm8
	vpaddq zmm4, zmm4, zmm9
	vpsrlq zmm11, zmm11, 32
	vpsrlq zmm12, zmm12, 32
	vpsrlq zmm13, zmm13, 32
	vpsrlq zmm14, zmm14, 32
	vpsrlq zmm15, zmm15, 32
	vpmuludq zmm5, zmm1, zmm15
	vpmuludq zmm10, zmm2, zmm14
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm3, zmm13
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm4, zmm12
	vpaddq zmm5, zmm5, zmm10
	vpsllq zmm10, zmm5, 2
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm10, zmm0, zmm11
	vpaddq zmm5, zmm5, zmm10
	vpmuludq zmm6, zmm2, zmm15
	vpmuludq zmm10, zmm3, zmm14
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm4, zmm13
	vpaddq zmm6, zmm6, zmm10
	vpsllq zmm10, zmm6, 2
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm0, zmm12
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm10, zmm1, zmm11
	vpaddq zmm6, zmm6, zmm10
	vpmuludq zmm7, zmm3, zmm15
	vpmuludq zmm10, zmm4, zmm14
	vpaddq zmm7, zmm7, zmm10
	vpsllq zmm10, zmm7, 2
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm0, zmm13
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm1, zmm12
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm10, zmm2, zmm11
	vpaddq zmm7, zmm7, zmm10
	vpmuludq zmm8, zmm4, zmm15
	vpsllq zmm10, zmm8, 2
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm0, zmm14
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm1, zmm13
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm2, zmm12
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm10, zmm3, zmm11
	vpaddq zmm8, zmm8, zmm10
	vpmuludq zmm9, zmm0, zmm15
	vpmuludq zmm10, zmm1, zmm14
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm2, zmm13
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm3, zmm12
	vpaddq zmm9, zmm9, zmm10
	vpmuludq zmm10, zmm4, zmm11
	vpaddq zmm9, zmm9, zmm10
	vmovq xmm4, r8
	vpbroadcastq zmm4, xmm4
	vpsrlq zmm10, zmm5, 26
	vpandq zmm0, zmm5, zmm4
	vpaddq zmm6, zmm6, zmm10
	vpsrlq zmm10, zmm6, 26
	vpandq zmm1, zmm6, zmm4
	vpaddq zmm7, zmm7, zmm10
	vpsrlq zmm10, zmm7, 26
	vpandq zmm2, zmm7, zmm4
	vpaddq zmm8, zmm8, zmm10
	vpsrlq zmm10, zmm8, 26
	vpandq zmm3, zmm8, zmm4
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm9, 26
	vmovdqa64 zmm5, zmm4
	vpandq zmm4, zmm9, zmm4
	vpsllq zmm6, zmm10, 2
	vpaddq zmm10, zmm10, zmm6
	vpaddq zmm0, zmm0, zmm10
	vpsrlq zmm10, zmm0, 26
	vpandq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm10
	vshufi32x4 zmm10, zmm0, zmm0, 238
	vpaddq zmm5, zmm0, zmm10
	vshufi32x4 zmm10, zmm5, zmm5, 1
	vpaddq zmm5, zmm5, zmm10
	vpunpckhqdq zmm10, zmm5, zmm5
	vpaddq zmm5, zmm5, zmm10
	vshufi32x4 zmm10, zmm1, zmm1, 238
	vpaddq zmm6, zmm1, zmm10
	vshufi32x4 zmm10, zmm6, zmm6, 1
	vpaddq zmm6, zmm6, zmm10
	vpunpckhqdq zmm10, zmm6, zmm6
	vpaddq zmm6, zmm6, zmm10
	vshufi32x4 zmm10, zmm2, zmm2, 238
	vpaddq zmm7, zmm2, zmm10
	vshufi32x4 zmm10, zmm7, zmm7, 1
	vpaddq zmm7, zmm7, zmm10
	vpunpckhqdq zmm10, zmm7, zmm7
	vpaddq zmm7, zmm7, zmm10
	vshufi32x4 zmm10, zmm3, zmm3, 238
	vpaddq zmm8, zmm3, zmm10
	vshufi32x4 zmm10, zmm8, zmm8, 1
	vpaddq zmm8, zmm8, zmm10
	vpunpckhqdq zmm10, zmm8, zmm8
	vpaddq zmm8, zmm8, zmm10
	vshufi32x4 zmm10, zmm4, zmm4, 238
	vpaddq zmm9, zmm4, zmm10
	vshufi32x4 zmm10, zmm9, zmm9, 1
	vpaddq zmm9, zmm9, zmm10
	vpunpckhqdq zmm10, zmm9, zmm9
	vpaddq zmm9, zmm9, zmm10
	vmovq xmm4, r8
	vpbroadcastq zmm4, xmm4
	vpsrlq zmm10, zmm5, 26
	vpandq zmm0, zmm5, zmm4
	vpaddq zmm6, zmm6, zmm10
	vpsrlq zmm10, zmm6, 26
	vpandq zmm1, zmm6, zmm4
	vpaddq zmm7, zmm7, zmm10
	vpsrlq zmm10, zmm7, 26
	vpandq zmm2, zmm7, zmm4
	vpaddq zmm8, zmm8, zmm10
	vpsrlq zmm10, zmm8, 26
	vpandq zmm3, zmm8, zmm4
	vpaddq zmm9, zmm9, zmm10
	vpsrlq zmm10, zmm9, 26
	vmovdqa64 zmm5, zmm4
	vpandq zmm4, zmm9, zmm4
	vpsllq zmm6, zmm10, 2
	vpaddq zmm10, zmm10, zmm6
	vpaddq zmm0, zmm0, zmm10
	vpsrlq zmm10, zmm0, 26
	vpandq zmm0, zmm0, zmm5
	vpaddq zmm1, zmm1, zmm10
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
	add rsi, 128
	and rdx, 7
	test rdx, rdx
	je 23f
	call {vg_poly1305_blocks}
	jmp 24f
23:
24:
	jmp 21f
20:
	call {vg_poly1305_blocks_avx2}
21:
	ret
	.p2align 6
