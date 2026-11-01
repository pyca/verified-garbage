// The functions of `src/internal/vg_poly1305_blocks_ifma.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_blocks_ifma:
	cmp rdx, 32
	jb 20f
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
	movabs r8, 17592186044415
	mov QWORD PTR [rdi+104], r8
	movabs rax, 1099511627776
	mov QWORD PTR [rdi+112], rax
	mov rax, r10
	and rax, r8
	mov rcx, r11
	shl rcx, 20
	mov r9, r10
	shr r9, 44
	or rcx, r9
	and rcx, r8
	mov r9, r11
	shr r9, 24
	vmovq xmm3, rax
	vpbroadcastq zmm3, xmm3
	vmovq xmm4, rcx
	vpbroadcastq zmm4, xmm4
	vmovq xmm5, r9
	vpbroadcastq zmm5, xmm5
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vmovdqa64 zmm0, zmm3
	vmovdqa64 zmm1, zmm4
	vmovdqa64 zmm2, zmm5
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	movq rax, xmm0
	mov QWORD PTR [rdi+56], rax
	movq rax, xmm1
	mov QWORD PTR [rdi+64], rax
	movq rax, xmm2
	mov QWORD PTR [rdi+72], rax
	vmovdqa64 zmm3, zmm0
	vmovdqa64 zmm4, zmm1
	vmovdqa64 zmm5, zmm2
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	movq rax, xmm0
	mov QWORD PTR [rdi+80], rax
	movq rax, xmm1
	mov QWORD PTR [rdi+88], rax
	movq rax, xmm2
	mov QWORD PTR [rdi+96], rax
	vmovdqa64 zmm3, zmm0
	vmovdqa64 zmm4, zmm1
	vmovdqa64 zmm5, zmm2
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	vmovdqa64 zmm3, zmm0
	vmovdqa64 zmm4, zmm1
	vmovdqa64 zmm5, zmm2
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	mov r9, QWORD PTR [rdi+16]
	shl r9, 40
	mov rcx, QWORD PTR [rdi+8]
	shr rcx, 24
	or r9, rcx
	mov rcx, QWORD PTR [rdi+8]
	shl rcx, 20
	mov rax, QWORD PTR [rdi]
	shr rax, 44
	or rcx, rax
	and rcx, r8
	mov rax, QWORD PTR [rdi]
	and rax, r8
	vmovq xmm0, rax
	vmovq xmm1, rcx
	vmovq xmm2, r9
	mov rcx, rdx
	shr rcx, 3
	sub rcx, 1
22:
	vmovdqu32 zmm14, ZMMWORD PTR [rsi]
	vmovdqu32 zmm15, ZMMWORD PTR [rsi+64]
	vpunpcklqdq zmm8, zmm14, zmm15
	vpunpckhqdq zmm9, zmm14, zmm15
	vpandq zmm14, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm0, zmm0, zmm14
	vpsrlq zmm14, zmm8, 44
	vpsllq zmm15, zmm9, 20
	vporq zmm14, zmm14, zmm15
	vpandq zmm14, zmm14, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	vpsrlq zmm14, zmm9, 24
	vporq zmm14, zmm14, QWORD PTR [rdi+112]{1to8}
	vpaddq zmm2, zmm2, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	add rsi, 128
	sub rcx, 1
	jne 22b
	vmovdqu32 zmm14, ZMMWORD PTR [rsi]
	vmovdqu32 zmm15, ZMMWORD PTR [rsi+64]
	vpunpcklqdq zmm8, zmm14, zmm15
	vpunpckhqdq zmm9, zmm14, zmm15
	vpandq zmm14, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm0, zmm0, zmm14
	vpsrlq zmm14, zmm8, 44
	vpsllq zmm15, zmm9, 20
	vporq zmm14, zmm14, zmm15
	vpandq zmm14, zmm14, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	vpsrlq zmm14, zmm9, 24
	vporq zmm14, zmm14, QWORD PTR [rdi+112]{1to8}
	vpaddq zmm2, zmm2, zmm14
	mov rax, QWORD PTR [rdi+80]
	mov rcx, QWORD PTR [rdi+88]
	mov r9, QWORD PTR [rdi+96]
	vmovq xmm3, rax
	vpbroadcastq zmm3, xmm3
	vmovq xmm4, rcx
	vpbroadcastq zmm4, xmm4
	vmovq xmm5, r9
	vpbroadcastq zmm5, xmm5
	vpxord zmm15, zmm15, zmm15
	vporq zmm14, zmm15, QWORD PTR [rdi+104]{1to8}
	vpsrlq zmm14, zmm14, 43
	vpunpcklqdq zmm3, zmm3, zmm14
	vpunpcklqdq zmm4, zmm4, zmm15
	vpunpcklqdq zmm5, zmm5, zmm15
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	vpunpckhqdq zmm14, zmm0, zmm0
	vpaddq zmm0, zmm0, zmm14
	vpunpckhqdq zmm14, zmm1, zmm1
	vpaddq zmm1, zmm1, zmm14
	vpunpckhqdq zmm14, zmm2, zmm2
	vpaddq zmm2, zmm2, zmm14
	mov rax, r10
	and rax, r8
	mov rcx, r11
	shl rcx, 20
	mov r9, r10
	shr r9, 44
	or rcx, r9
	and rcx, r8
	mov r9, r11
	shr r9, 24
	vmovq xmm3, rax
	vpbroadcastq zmm3, xmm3
	vmovq xmm4, rcx
	vpbroadcastq zmm4, xmm4
	vmovq xmm5, r9
	vpbroadcastq zmm5, xmm5
	vpxord zmm15, zmm15, zmm15
	vporq zmm14, zmm15, QWORD PTR [rdi+104]{1to8}
	vpsrlq zmm14, zmm14, 43
	vshufi32x4 zmm3, zmm3, zmm14, 0
	vshufi32x4 zmm4, zmm4, zmm15, 0
	vshufi32x4 zmm5, zmm5, zmm15, 0
	vshufi32x4 zmm3, zmm3, zmm3, 136
	vshufi32x4 zmm4, zmm4, zmm4, 136
	vshufi32x4 zmm5, zmm5, zmm5, 136
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	vshufi32x4 zmm14, zmm0, zmm0, 245
	vpaddq zmm0, zmm0, zmm14
	vshufi32x4 zmm14, zmm1, zmm1, 245
	vpaddq zmm1, zmm1, zmm14
	vshufi32x4 zmm14, zmm2, zmm2, 245
	vpaddq zmm2, zmm2, zmm14
	mov rax, QWORD PTR [rdi+56]
	mov rcx, QWORD PTR [rdi+64]
	mov r9, QWORD PTR [rdi+72]
	vmovq xmm3, rax
	vpbroadcastq zmm3, xmm3
	vmovq xmm4, rcx
	vpbroadcastq zmm4, xmm4
	vmovq xmm5, r9
	vpbroadcastq zmm5, xmm5
	vpxord zmm15, zmm15, zmm15
	vporq zmm14, zmm15, QWORD PTR [rdi+104]{1to8}
	vpsrlq zmm14, zmm14, 43
	vshufi32x4 zmm3, zmm3, zmm14, 0
	vshufi32x4 zmm4, zmm4, zmm15, 0
	vshufi32x4 zmm5, zmm5, zmm15, 0
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	vshufi32x4 zmm14, zmm0, zmm0, 238
	vpaddq zmm0, zmm0, zmm14
	vshufi32x4 zmm14, zmm1, zmm1, 238
	vpaddq zmm1, zmm1, zmm14
	vshufi32x4 zmm14, zmm2, zmm2, 238
	vpaddq zmm2, zmm2, zmm14
	mov rax, r10
	and rax, r8
	mov rcx, r11
	shl rcx, 20
	mov r9, r10
	shr r9, 44
	or rcx, r9
	and rcx, r8
	mov r9, r11
	shr r9, 24
	vmovq xmm3, rax
	vpbroadcastq zmm3, xmm3
	vmovq xmm4, rcx
	vpbroadcastq zmm4, xmm4
	vmovq xmm5, r9
	vpbroadcastq zmm5, xmm5
	vpsllq zmm6, zmm4, 4
	vpsllq zmm14, zmm4, 2
	vpaddq zmm6, zmm6, zmm14
	vpsllq zmm7, zmm5, 4
	vpsllq zmm14, zmm5, 2
	vpaddq zmm7, zmm7, zmm14
	vpxord zmm8, zmm8, zmm8
	vpxord zmm11, zmm11, zmm11
	vpxord zmm9, zmm9, zmm9
	vpxord zmm12, zmm12, zmm12
	vpxord zmm10, zmm10, zmm10
	vpxord zmm13, zmm13, zmm13
	vpmadd52luq zmm8, zmm0, zmm3
	vpmadd52huq zmm11, zmm0, zmm3
	vpmadd52luq zmm9, zmm0, zmm4
	vpmadd52huq zmm12, zmm0, zmm4
	vpmadd52luq zmm10, zmm0, zmm5
	vpmadd52huq zmm13, zmm0, zmm5
	vpmadd52luq zmm8, zmm1, zmm7
	vpmadd52huq zmm11, zmm1, zmm7
	vpmadd52luq zmm9, zmm1, zmm3
	vpmadd52huq zmm12, zmm1, zmm3
	vpmadd52luq zmm10, zmm1, zmm4
	vpmadd52huq zmm13, zmm1, zmm4
	vpmadd52luq zmm8, zmm2, zmm6
	vpmadd52huq zmm11, zmm2, zmm6
	vpmadd52luq zmm9, zmm2, zmm7
	vpmadd52huq zmm12, zmm2, zmm7
	vpmadd52luq zmm10, zmm2, zmm3
	vpmadd52huq zmm13, zmm2, zmm3
	vpsllq zmm14, zmm11, 8
	vpaddq zmm9, zmm9, zmm14
	vpsllq zmm14, zmm12, 8
	vpaddq zmm10, zmm10, zmm14
	vpsllq zmm14, zmm13, 12
	vpaddq zmm8, zmm8, zmm14
	vpsllq zmm14, zmm13, 10
	vpaddq zmm8, zmm8, zmm14
	vpsrlq zmm14, zmm8, 44
	vpandq zmm0, zmm8, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm9, zmm9, zmm14
	vpsrlq zmm14, zmm9, 44
	vpandq zmm1, zmm9, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm10, zmm10, zmm14
	vpsrlq zmm14, zmm10, 44
	vpandq zmm2, zmm10, QWORD PTR [rdi+104]{1to8}
	vpsllq zmm15, zmm14, 4
	vpaddq zmm0, zmm0, zmm15
	vpsllq zmm15, zmm14, 2
	vpaddq zmm0, zmm0, zmm15
	vpsrlq zmm14, zmm0, 44
	vpandq zmm0, zmm0, QWORD PTR [rdi+104]{1to8}
	vpaddq zmm1, zmm1, zmm14
	lfence
	ldmxcsr DWORD PTR [rdi+120]
	vzeroupper
	mov QWORD PTR [rdi+72], rbx
	mov QWORD PTR [rdi+80], rbp
	mov QWORD PTR [rdi+88], r12
	mov QWORD PTR [rdi+96], r13
	mov QWORD PTR [rdi+104], r14
	mov QWORD PTR [rdi+112], r15
	movq r11, xmm0
	movq rax, xmm1
	movq rcx, xmm2
	mov rbx, rax
	shl rax, 44
	shr rbx, 20
	mov rbp, rcx
	shl rcx, 24
	shr rbp, 40
	add r11, rax
	adc rbx, rcx
	adc rbp, 0
	mov rax, rbp
	and rbp, 3
	shr rax, 2
	mov rcx, rax
	shl rcx, 2
	add rax, rcx
	add r11, rax
	adc rbx, 0
	adc rbp, 0
	mov r9, rdx
	mov rax, r11
	add rax, 5
	mov rdx, rbx
	adc rdx, 0
	mov r12, rbp
	adc r12, 0
	mov r13, r12
	shr r13, 2
	mov r14d, 0
	sub r14, r13
	and r12, 3
	xor rax, r11
	and rax, r14
	xor r11, rax
	xor rdx, rbx
	and rdx, r14
	xor rbx, rdx
	xor r12, rbp
	and r12, r14
	xor rbp, r12
	mov QWORD PTR [rdi], r11
	mov QWORD PTR [rdi+8], rbx
	mov QWORD PTR [rdi+16], rbp
	mov rbx, QWORD PTR [rdi+72]
	mov rbp, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+88]
	mov r13, QWORD PTR [rdi+96]
	mov r14, QWORD PTR [rdi+104]
	mov r15, QWORD PTR [rdi+112]
	mov rdx, r9
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
